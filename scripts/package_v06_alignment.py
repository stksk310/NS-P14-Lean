#!/usr/bin/env python3
"""Publish an immutable V06 archive only after source/evidence/verifier review.

Review JSON fields are intentionally V06-specific; Run18 COMPLETE metadata is
neither read nor copied as this alignment's authority. The review report and
decision live in a separate new v06_alignment_* evidence directory.
"""
from pathlib import Path
import argparse
import gzip
import importlib.util
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('v06_verify', ROOT / 'scripts/verify_v06_alignment.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def checked_payload(root, verification, review):
    vdir = verify.safe(root, verification)
    if not verify.is_new_evidence(verification + '/verification.json'):
        raise ValueError('V06 evidence directory required')
    review_path = verify.safe(root, review)
    if not verify.is_new_evidence(review) or review_path.is_relative_to(vdir):
        raise ValueError('review must be separate, new V06 evidence')
    summary = json.loads((vdir / 'verification.json').read_text())
    decision = json.loads(review_path.read_text())
    if summary.get('status') != 'V06_ALIGNMENT_COMPLETE' or summary.get('v06_alignment_complete') is not True:
        raise ValueError('V06 alignment is not complete')
    if summary.get('scope') != verify.SCOPE or summary.get('baseline_commit') != verify.BASE:
        raise ValueError('alignment scope or baseline differs')
    if summary.get('fresh_whole_project_cache') is not True or summary.get('base_public_types_preserved') is not True:
        raise ValueError('cold build and base public-type comparison required')
    if set(summary.get('normal_explicit_type_and_axiom_coverage', [])) != verify.AUDITED_MODULES:
        raise ValueError('modified/new module audit coverage differs')
    if set(summary.get('verified_import_only_modules', [])) != verify.IMPORT_ONLY_MODULES:
        raise ValueError('import-only module audit coverage differs')
    if not summary.get('checks') or not all(c.get('passed') is True and c.get('exit_code') == 0 for c in summary['checks']):
        raise ValueError('validation checks failed')
    if summary.get('inherited_command_count') != 280 or summary.get('inherited_run18_complete_preserved') is not True:
        raise ValueError('inherited validation scope missing')
    if (decision.get('verdict') != 'PASS' or any(decision.get(k) != 0 for k in ['critical', 'important', 'minor'])
            or decision.get('v06_alignment_complete') is not True or decision.get('scope') != verify.SCOPE
            or decision.get('pending') != [] or decision.get('declined') != []):
        raise ValueError('independent alignment review failed or scope differs')
    if decision.get('verifier_independently_reviewed') is not True:
        raise ValueError('alignment verifier independent review required')
    if decision.get('proof_snapshot_commit') != summary['proof_snapshot_commit']:
        raise ValueError('review proof snapshot differs')
    for field, file in [('verification_summary_sha256', 'verification.json'),
                        ('verification_manifest_sha256', 'MANIFEST_SHA256.json'),
                        ('source_manifest_sha256', 'SOURCE_SHA256.json')]:
        if decision.get(field) != verify.sha((vdir / file).read_bytes()):
            raise ValueError('review hash differs: ' + file)
    report_path = verify.safe(root, decision['review_report'])
    if not verify.is_new_evidence(decision['review_report']) or report_path.is_relative_to(vdir):
        raise ValueError('review report must be separate new V06 evidence')
    if decision.get('review_report_sha256') != verify.sha(report_path.read_bytes()):
        raise ValueError('review report changed')
    source = json.loads((vdir / 'SOURCE_SHA256.json').read_text())
    evidence = json.loads((vdir / 'MANIFEST_SHA256.json').read_text())
    verify.check_source_manifest(root, source, summary['proof_snapshot_commit'])
    verify.check_evidence_manifest(root, vdir, evidence)
    verify.validate_changes(root)
    if set(source) & set(evidence):
        raise ValueError('source/evidence collision')
    declarations = json.loads(gzip.decompress((vdir / 'declarations.json.gz').read_bytes()))
    base = json.loads(gzip.decompress((vdir / 'base_declarations.json.gz').read_bytes()))
    raw, metadata = verify.parse_audit(gzip.decompress((vdir / 'environment_axioms.log.gz').read_bytes()).decode())
    verify.validate_import_coverage(metadata, verify.AUDITED_MODULES | verify.IMPORT_ONLY_MODULES)
    verify.validate_audit(declarations, verify.AUDITED_MODULES, base, expected_names={r['name'] for r in raw})
    by_name = {r['name']: r for r in declarations}
    for original in raw:
        saved = by_name[original['name']]
        for key in ['name', 'module', 'axioms', 'type', 'explicit_type']:
            if saved.get(key) != original.get(key):
                raise ValueError('saved declaration differs from raw environment audit: ' + original['name'])
        if saved.get('exported_kind') != original['kind']:
            raise ValueError('saved declaration kind differs from raw audit')
    # Exactly the fixed R16 inventory must appear in the replay map and checks.
    old = json.loads((root / verify.R16 / 'verification.json').read_text())
    mapping = json.loads((vdir / 'COMMAND_MAP.json').read_text())
    if len(mapping) != 280 or [m['name'] for m in mapping] != [c['name'] for c in old['checks']]:
        raise ValueError('R16 replay map coverage differs')
    records = {r['name']: r for r in summary['checks']}
    for prior, mapped in zip(old['checks'], mapping):
        expected = [s.replace(verify.R16 + '/', verification + '/') for s in prior['command']]
        if mapped['old_command'] != prior['command'] or mapped['new_command'] != expected or records.get(prior['name'], {}).get('command') != expected:
            raise ValueError('R16 command mapping changed: ' + prior['name'])
    payload = {}
    proof = summary['proof_snapshot_commit']
    evidence_commit = decision['evidence_commit']
    reviewed_commit = decision['reviewed_commit']
    for older, newer in [(proof, evidence_commit), (evidence_commit, reviewed_commit)]:
        if subprocess.run(['git', 'merge-base', '--is-ancestor', older, newer], cwd=root).returncode:
            raise ValueError('proof/evidence/reviewed commit ancestry differs')
    for name, digest in source.items():
        data = verify.safe(root, name).read_bytes()
        for commit in [proof, evidence_commit, reviewed_commit]:
            if verify.sha(verify.git(root, 'show', commit + ':' + name)) != digest:
                raise ValueError('committed source bytes differ: ' + name)
        payload[name] = data
    # The evidence commit and independently reviewed commit both bind every raw
    # log, declaration record, map, manifest, and environmental observation.
    manifest_name = str(Path(verification) / 'MANIFEST_SHA256.json')
    for name in list(evidence) + [manifest_name]:
        data = verify.safe(root, name).read_bytes()
        for commit in [evidence_commit, reviewed_commit]:
            if verify.git(root, 'show', commit + ':' + name) != data:
                raise ValueError('committed evidence bytes differ: ' + name)
        payload[name] = data
    for name in [review, decision['review_report']]:
        data = verify.safe(root, name).read_bytes()
        # Review files may be committed after reviewed_commit (to avoid circular
        # commit IDs), but must exist unchanged in the current publication HEAD.
        if verify.git(root, 'show', 'HEAD:' + name) != data:
            raise ValueError('review file is not committed: ' + name)
        payload[name] = data
    return payload, summary, decision


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verification', required=True)
    parser.add_argument('--review', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        target = verify.safe(ROOT, args.output)
        if not verify.is_new_archive(args.output) or target.exists():
            raise ValueError('new artifacts/NS_P14_V06_ALIGNMENT_*.zip required')
        payload, summary, decision = checked_payload(ROOT, args.verification, args.review)
        manifest = {name: verify.sha(data) for name, data in sorted(payload.items())}
        payload['BUNDLE_SHA256.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
        payload['V06_ALIGNMENT_RECEIPT.json'] = (json.dumps({
            'status': 'V06_ALIGNMENT_COMPLETE', 'scope': verify.SCOPE,
            'proof_snapshot_commit': summary['proof_snapshot_commit'],
            'evidence_commit': decision['evidence_commit'], 'reviewed_commit': decision['reviewed_commit'],
            'publication_head': verify.git(ROOT, 'rev-parse', 'HEAD').decode().strip(),
            'verification': args.verification, 'review': args.review,
            'not_claimed': ['N4', 'Run19', 'all_P14'],
        }, indent=2) + '\n').encode()
        # Receipt itself is covered by the manifest, without circular hashing.
        manifest['V06_ALIGNMENT_RECEIPT.json'] = verify.sha(payload['V06_ALIGNMENT_RECEIPT.json'])
        payload['BUNDLE_SHA256.json'] = (json.dumps(dict(sorted(manifest.items())), indent=2) + '\n').encode()
        target.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_DEFLATED) as archive:
            for name, data in sorted(payload.items()):
                archive.writestr(name, data)
        with zipfile.ZipFile(target) as archive:
            if archive.testzip() is not None or len(archive.namelist()) != len(set(archive.namelist())) or set(archive.namelist()) != set(payload):
                raise ValueError('archive CRC or fileset check failed')
            if any(verify.sha(archive.read(n)) != h for n, h in manifest.items()):
                raise ValueError('archive content hashes differ')
        print(json.dumps({'status': 'PUBLISHED_V06_ALIGNMENT_BUNDLE', 'archive': args.output,
                          'archive_sha256': verify.sha(target.read_bytes()), 'entries': len(payload),
                          'crc': 'PASS', 'scope': verify.SCOPE}, indent=2))
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as exc:
        parser.exit(1, str(exc) + '\n')


if __name__ == '__main__':
    main()
