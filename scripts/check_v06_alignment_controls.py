#!/usr/bin/env python3
"""Exercise the V06 verifier's guards in a disposable, independently copied tree."""
from pathlib import Path
import argparse
import copy
import importlib.util
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('v06_verify', ROOT / 'scripts/verify_v06_alignment.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        output = verify.safe(ROOT, args.output)
        if not verify.is_new_evidence(args.output) or output.exists():
            raise ValueError('new evidence file under v06_alignment_* required')
        results = []
        def reject(name, action, contains):
            try:
                action()
            except ValueError as exc:
                if contains not in str(exc):
                    raise ValueError(name + ': wrong rejection: ' + str(exc)) from exc
                results.append({'control': name, 'passed': True, 'rejection': str(exc)})
            else:
                raise ValueError(name + ': invalid input was accepted')
        with tempfile.TemporaryDirectory(prefix='nsp14-v06-controls-') as name:
            isolated = Path(name) / 'repository'
            # No checkout, commit, hardlink or build. Copy source and evidence
            # bytes; share only read-only Git objects through clone alternates.
            clone = subprocess.run(['git', 'clone', '--shared', '--no-checkout', str(ROOT), str(isolated)],
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if clone.returncode:
                raise ValueError('disposable clone failed: ' + clone.stdout)
            # Populate only the disposable index, so tracked ignored files (the
            # inherited paper PDFs) remain part of its fileset. No checkout.
            subprocess.run(['git', 'read-tree', 'HEAD'], cwd=isolated, check=True)
            for child in ROOT.iterdir():
                if child.name in {'.git', '.lake', '__pycache__'}:
                    continue
                target = isolated / child.name
                if child.is_dir():
                    shutil.copytree(child, target, symlinks=True, ignore=shutil.ignore_patterns('__pycache__'))
                elif child.is_file():
                    shutil.copy2(child, target)
            verify.validate_changes(isolated, require_new=False)
            results.append({'control': 'unaltered_disposable_snapshot', 'passed': True})
            reject('absolute_output', lambda: verify.validate_output(isolated, '/tmp/v06_alignment_escape'), 'unsafe relative path')
            reject('parent_traversal_output', lambda: verify.validate_output(isolated, 'verification/run18/runs/../v06_alignment_escape'), 'unsafe relative path')
            reject('old_evidence_output', lambda: verify.validate_output(isolated, verify.R16), 'unique verification')
            existing = 'verification/run18/runs/v06_alignment_existing_control'
            (isolated / existing).mkdir(exist_ok=True)
            reject('existing_output', lambda: verify.validate_output(isolated, existing), 'already exists')
            alias = isolated / 'verification/run18/runs/v06_alignment_alias_control'
            alias.symlink_to(isolated / existing, target_is_directory=True)
            reject('internal_symlink_output', lambda: verify.validate_output(isolated, str(alias.relative_to(isolated))), 'symlink path')
            alias.unlink()
            alias.symlink_to(Path(name), target_is_directory=True)
            reject('external_symlink_output', lambda: verify.validate_output(isolated, str(alias.relative_to(isolated))), 'symlink path')
            alias.unlink()
            frozen = isolated / 'audit/run18/RequestedGoals.lean'
            original = frozen.read_bytes()
            frozen.write_bytes(original + b'\n-- disposable mutation\n')
            reject('forbidden_inherited_source_edit', lambda: verify.validate_changes(isolated, require_new=False), 'forbidden inherited edit')
            frozen.write_bytes(original)
            old_evidence = isolated / verify.R16 / 'verification.json'
            original = old_evidence.read_bytes()
            old_evidence.write_bytes(original + b'\n')
            reject('inherited_evidence_edit', lambda: verify.validate_changes(isolated, require_new=False), 'forbidden inherited edit')
            old_evidence.write_bytes(original)
            sources = verify.source_manifest(isolated)
            source = isolated / 'scripts/verify_v06_alignment.py'
            original = source.read_bytes()
            source.write_bytes(original + b'\n# disposable mutation\n')
            reject('source_manifest_edit', lambda: verify.check_source_manifest(isolated, sources), 'source manifest')
            source.write_bytes(original)
            extra_source = isolated / 'NSP14/UnlistedV06Control.lean'
            extra_source.write_text('module\n')
            reject('source_fileset_addition', lambda: verify.validate_changes(isolated, require_new=False), 'finite allowlist')
            extra_source.unlink()
            evidence = isolated / existing
            (evidence / 'sample.json').write_text('{}\n')
            manifest = verify.evidence_manifest(isolated, evidence)
            (evidence / 'sample.json').write_text('{"changed":true}\n')
            reject('evidence_manifest_edit', lambda: verify.check_evidence_manifest(isolated, evidence, manifest), 'evidence manifest')
            (evidence / 'sample.json').write_text('{}\n')
            (evidence / 'unmanifested.txt').write_text('extra\n')
            reject('evidence_fileset_addition', lambda: verify.check_evidence_manifest(isolated, evidence, manifest), 'evidence manifest')
            endpoint = 'NSP14.Endpoint.CompetitorBounds'
            fresh = 'NSP14.Width.HigherFromSecond'
            rows = [{'name': 'Control.existing', 'module': endpoint, 'kind': 'axiom',
                     'type': 'True', 'explicit_type': 'True', 'axioms': ['propext']},
                    {'name': 'Control.new', 'module': fresh, 'kind': 'theorem',
                     'type': 'True', 'explicit_type': 'True', 'axioms': []}]
            required = {endpoint, fresh}
            verify.validate_audit(rows, required, [rows[0]])
            results.append({'control': 'public_proof_stub_is_accepted', 'passed': True})
            reject('modified_old_module_omission', lambda: verify.validate_audit(rows[1:], required), 'module type coverage')
            for key in ['type', 'explicit_type', 'axioms']:
                altered = copy.deepcopy(rows)
                del altered[0][key]
                reject('modified_old_declaration_missing_' + key, lambda: verify.validate_audit(altered, required),
                       'axiom audit coverage' if key == 'axioms' else 'module type coverage')
            altered = copy.deepcopy(rows)
            altered[0]['axioms'] = ['Control.extraAxiom']
            reject('extra_transitive_axiom', lambda: verify.validate_audit(altered, required), 'unapproved or self axiom')
            altered[0]['axioms'] = ['Control.existing']
            reject('self_axiom_dependency', lambda: verify.validate_audit(altered, required), 'unapproved or self axiom')
            altered = copy.deepcopy(rows)
            altered[0]['explicit_type'] = 'False'
            reject('base_public_type_changed', lambda: verify.validate_audit(altered, required, [rows[0]]), 'base export type changed')
            reject('base_public_export_removed', lambda: verify.validate_audit(rows[1:], {fresh}, [rows[0]]), 'base export removed')
            reject('new_declaration_row_omitted', lambda: verify.validate_audit(rows[:1], {endpoint}, expected_names={r['name'] for r in rows}), 'declaration fileset coverage')
            reject('empty_import_module_missing', lambda: verify.validate_import_coverage({'imported_modules': list(required)}, required | {'NSP14'}), 'imported-module coverage')
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('x') as stream:
            json.dump({'status': 'PASS_V06_ALIGNMENT_NEGATIVE_CONTROLS',
                       'disposable_isolated_environment': True, 'checkout_commit_or_build_performed': False,
                       'controls': results, 'count': len(results)}, stream, ensure_ascii=False, indent=2)
            stream.write('\n')
        print('PASS_V06_ALIGNMENT_NEGATIVE_CONTROLS', len(results))
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, str(exc) + '\n')


if __name__ == '__main__':
    main()
