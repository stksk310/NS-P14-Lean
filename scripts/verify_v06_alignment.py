#!/usr/bin/env python3
"""Cold, source-bound V06 alignment verification; inherited certificates are read-only.

The constants below are a finite preimplementation policy, not a diff-derived allowlist.
Use --preflight for a cheap policy check. A complete run requires a committed proof
snapshot and --fresh-project-cache. No old verifier is rerun in place.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import tarfile
import tempfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
BASE = 'a7504eea25f02728d1be6cd0082e8484d639dbe2'
R16 = 'verification/run18/runs/release_candidate_20261115_r16'
FROZEN = '86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
MATHLIB = '139105d28c7685a154cb3093f79edb2e16708099'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MODIFIED = {
    'NSP14/Endpoint/CompetitorBounds.lean', 'NSP14/Endpoint/CarrySums.lean',
    'NSP14/Endpoint/FiniteSocleBounds.lean', 'NSP14/Endpoint/FiniteCompetitors.lean',
    'NSP14/Width/AntipodalComparison.lean', 'NSP14/Width/FiveNonAntipodal.lean',
    'NSP14/Width/FiveHigher.lean', 'NSP14/Width/SparseHigher.lean',
    'NSP14/Width/DenseLexResources.lean', 'NSP14/Width/DensePayment.lean',
    'NSP14/Width/DenseComparison.lean',
}
APPEND_ONLY = {'NSP14.lean', 'LEAN_PROGRESS.md', 'docs/LEAN_PAPER_ALIGNMENT_JA.md'}
NEW_PRODUCTION = {'NSP14/Width/IntegerPayment.lean', 'NSP14/Width/HigherFromSecond.lean'}
NEW_FIXTURES = {
    'tests/V06Endpoint.lean', 'tests/V06IntegerPayment.lean',
    'tests/V06HigherFromSecond.lean', 'tests/V06Dense.lean',
    'audit/v06_alignment/RouteChecks.lean',
}
NEW_INFRASTRUCTURE = {
    'scripts/verify_v06_alignment.py', 'scripts/check_v06_alignment_controls.py',
    'scripts/package_v06_alignment.py', 'scripts/check_v06_routes.py',
    'docs/V06_ALIGNMENT_PLAN_JA.md', 'docs/V06_ALIGNMENT_LEDGER_JA.md',
    'docs/V06_ALIGNMENT_HANDOFF_JA.md', 'docs/V06_ALIGNMENT_CHANGE_POLICY.json',
}
NEW_FILES = NEW_PRODUCTION | NEW_FIXTURES | NEW_INFRASTRUCTURE
IMPORT_ONLY_MODULES = {'NSP14', 'audit.v06_alignment.RouteChecks'}
AUDITED_MODULES = {p[:-5].replace('/', '.') for p in MODIFIED | NEW_PRODUCTION | NEW_FIXTURES} - IMPORT_ONLY_MODULES
SCOPE = ['endpoint', 'antipodal_integer_payment', 'nonantipodal_integer_payment',
         'higher_from_second', 'dense_two_branches']
TOKEN = re.compile(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b', re.M)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def safe(root, name):
    p = Path(name)
    if not name or p.is_absolute() or '..' in p.parts or '\\' in name:
        raise ValueError('unsafe relative path: ' + str(name))
    result = root / p
    current = root
    for part in p.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError('symlink path is forbidden: ' + name)
    if not result.resolve().is_relative_to(root.resolve()):
        raise ValueError('path escapes repository: ' + name)
    return result


def validate_output(root, name):
    p = Path(name)
    target = safe(root, name)
    if len(p.parts) != 4 or p.parts[:3] != ('verification', 'run18', 'runs') or not re.fullmatch(r'v06_alignment_[A-Za-z0-9_-]+', p.name):
        raise ValueError('a unique verification/run18/runs/v06_alignment_* directory is required')
    if target.exists():
        raise ValueError('output already exists; evidence is immutable')
    return target


def base_tree(root):
    rows = git(root, 'ls-tree', '-r', BASE).decode().splitlines()
    return {line.split('\t', 1)[1]: line.split()[2] for line in rows}


def blob_oid(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def current_files(root):
    raw = git(root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard')
    return {p for p in raw.decode().split('\0') if p}


def is_new_evidence(name):
    p = Path(name)
    return (len(p.parts) >= 5 and p.parts[:3] == ('verification', 'run18', 'runs')
            and re.fullmatch(r'v06_alignment_[A-Za-z0-9_-]+', p.parts[3]) is not None)


def is_new_archive(name):
    p = Path(name)
    return len(p.parts) == 2 and p.parts[0] == 'artifacts' and re.fullmatch(r'NS_P14_V06_ALIGNMENT_[A-Za-z0-9_-]+\.zip', p.name) is not None


def validate_changes(root, require_new=True):
    old = base_tree(root)
    actual = current_files(root)
    if not set(old) <= actual:
        raise ValueError('inherited files missing: ' + repr(sorted(set(old) - actual)))
    for name, oid in old.items():
        p = safe(root, name)
        if not p.is_file() or p.is_symlink():
            raise ValueError('inherited file missing or symlink: ' + name)
        data = p.read_bytes()
        if name in APPEND_ONLY:
            if not data.startswith(git(root, 'show', BASE + ':' + name)):
                raise ValueError('append-only prefix changed: ' + name)
        elif name not in MODIFIED and blob_oid(data) != oid:
            raise ValueError('forbidden inherited edit: ' + name)
    extra = actual - set(old) - NEW_FILES
    extra = {p for p in extra if not is_new_evidence(p) and not is_new_archive(p)}
    if extra:
        raise ValueError('files outside finite allowlist: ' + repr(sorted(extra)))
    if require_new and not NEW_FILES <= actual:
        raise ValueError('required new files missing: ' + repr(sorted(NEW_FILES - actual)))
    policy_path = root / 'docs/V06_ALIGNMENT_CHANGE_POLICY.json'
    if policy_path.exists():
        policy = json.loads(policy_path.read_text())
        if (policy.get('base') != BASE or set(policy.get('modified_files', [])) != MODIFIED
                or set(policy.get('new_files', [])) != NEW_FILES or set(policy.get('append_only', [])) != APPEND_ONLY):
            raise ValueError('reviewed finite policy differs from verifier constants')
    if sha((root / 'audit/run18/RequestedGoals.lean').read_bytes()) != FROZEN:
        raise ValueError('frozen RequestedGoals changed')
    for name in MODIFIED | NEW_PRODUCTION | NEW_FIXTURES | {'NSP14.lean'}:
        p = root / name
        if p.exists() and TOKEN.search(p.read_text()):
            raise ValueError('forbidden proof token: ' + name)
    return old


def source_manifest(root):
    # Bind all tracked/new policy sources, scripts, docs and configuration, not
    # a historical hand-written subset. Evidence is independently manifested.
    names = {n for n in current_files(root) if Path(n).parts[0] not in {'verification', 'artifacts'}}
    return {n: sha(safe(root, n).read_bytes()) for n in sorted(names)}


def check_source_manifest(root, manifest, proof_commit=None):
    if source_manifest(root) != manifest:
        raise ValueError('source manifest content or fileset changed')
    if proof_commit:
        for name, digest in manifest.items():
            if sha(git(root, 'show', proof_commit + ':' + name)) != digest:
                raise ValueError('source is not committed in proof snapshot: ' + name)


def evidence_manifest(root, out):
    return {str(p.relative_to(root)): sha(p.read_bytes()) for p in sorted(out.rglob('*'))
            if p.is_file() and p != out / 'MANIFEST_SHA256.json'}


def check_evidence_manifest(root, out, manifest):
    if evidence_manifest(root, out) != manifest:
        raise ValueError('evidence manifest content or fileset changed')


def validate_audit(rows, required_modules, base_rows=None, expected_names=None):
    if not rows or len({r['name'] for r in rows}) != len(rows):
        raise ValueError('empty or duplicate declaration audit')
    if expected_names is not None and {r['name'] for r in rows} != set(expected_names):
        raise ValueError('environment declaration fileset coverage differs')
    coverage = {r['module'] for r in rows if 'type' in r and 'explicit_type' in r}
    if not required_modules <= coverage:
        raise ValueError('modified/new module type coverage missing: ' + repr(sorted(required_modules - coverage)))
    for row in rows:
        if 'axioms' not in row:
            raise ValueError('axiom audit coverage missing: ' + row['name'])
        if set(row['axioms']) - ALLOWED_AXIOMS or row['name'] in row['axioms']:
            raise ValueError('unapproved or self axiom dependency: ' + row['name'])
        if row['module'] in required_modules and ('type' not in row or 'explicit_type' not in row):
            raise ValueError('declaration type coverage missing: ' + row['name'])
    if base_rows is not None:
        current = {r['name']: r for r in rows}
        for old in base_rows:
            # Private implementation names are not public exports. Every other
            # declaration of each edited module is compared, including definitions.
            if old['name'].startswith('_private.'):
                continue
            now = current.get(old['name'])
            if now is None:
                raise ValueError('base export removed: ' + old['name'])
            for key in ['type', 'explicit_type']:
                if key not in old or old[key] != now.get(key):
                    raise ValueError('base export type changed: ' + old['name'] + ' (' + key + ')')


def parse_audit(raw):
    objects = [json.loads(line) for line in raw.splitlines() if line.startswith('{')]
    metadata = [row for row in objects if row.get('audit_metadata') is True]
    if len(metadata) != 1:
        raise ValueError('environment import coverage metadata missing')
    return [row for row in objects if row.get('audit_metadata') is not True], metadata[0]


def validate_import_coverage(metadata, required_modules):
    if not required_modules <= set(metadata.get('imported_modules', [])):
        raise ValueError('environment imported-module coverage missing')


def audit_source(imports, typed_modules, only_typed=False):
    return '''module
''' + ''.join('import ' + m + '\n' for m in sorted(set(imports))) + '''import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let typed : Array String := #["''' + '\",\"'.join(sorted(typed_modules)) + '''"]
 IO.println ((Json.mkObj [("audit_metadata",toJson true),("imported_modules",toJson (env.header.moduleNames.map Name.toString))]).compress)
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if ''' + ('typed.contains modName' if only_typed else 'modName == "NSP14" || modName.startsWith "NSP14." || modName == "tests" || modName.startsWith "tests." || modName.startsWith "audit."') + ''' then
   let axs ← collectAxioms n
   let kind := match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
   let mut fields := [("name",toJson n.toString),("module",toJson modName),("kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if typed.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
'''


def fixture_order(root, paths):
    result, active = [], set()
    def emit(name):
        if name in result:
            return
        if name in active:
            raise ValueError('fixture import cycle: ' + name)
        active.add(name)
        for module in re.findall(r'^\s*(?:public\s+)?import\s+((?:tests|audit)\.[\w.]+)', (root / name).read_text(), re.M):
            emit(module.replace('.', '/') + '.lean')
        active.remove(name)
        result.append(name)
    for name in paths:
        emit(name)
    return result


def preserve_evidence(root, excluded):
    return {str(p.relative_to(root)): sha(p.read_bytes()) for folder in ['verification', 'artifacts']
            for p in (root / folder).rglob('*') if p.is_file() and not p.is_relative_to(excluded)}


def baseline_audit(root, out, run, cache_donor=None):
    scratch = Path(tempfile.mkdtemp(prefix='nsp14-v06-base-'))
    paths = ['NSP14', 'NSP14.lean', 'tests', 'audit', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
    archive = git(root, 'archive', BASE, *paths)
    with tarfile.open(fileobj=io.BytesIO(archive)) as archive_file:
        archive_file.extractall(scratch, filter='data')
    (scratch / '.lake').mkdir(exist_ok=True)
    (scratch / '.lake/packages').symlink_to((root / '.lake/packages').resolve(), target_is_directory=True)
    if cache_donor:
        donor = Path(cache_donor).resolve()
        donor_root = donor.parents[1] if donor.name == 'build' and donor.parent.name == '.lake' else None
        if donor_root is None:
            raise ValueError('--baseline-cache must name a .lake/build directory')
        # Verify donor source identity before copying. Lake then checks/rebuilds
        # the isolated copy. No donor build files or shared mathlib are modified.
        old = base_tree(root)
        for name in old:
            if name == 'NSP14.lean' or name.startswith('NSP14/') or name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
                if not (donor_root / name).is_file() or blob_oid((donor_root / name).read_bytes()) != old[name]:
                    raise ValueError('baseline cache donor source mismatch: ' + name)
        shutil.copytree(donor, scratch / '.lake/build', symlinks=True)
    run('base_build', ['lake', 'build', 'NSP14', 'Mathlib.Algebra.Field.ZMod'], cwd=scratch)
    mods = {n[:-5].replace('/', '.') for n in MODIFIED}
    text = audit_source(['NSP14'], mods, only_typed=True)
    (scratch / 'BaseEnvironmentAudit.lean').write_text(text)
    (out / 'BaseEnvironmentAudit.lean').write_text(text)
    raw = run('base_environment_types', ['lake', 'env', 'lean', '-j1', '-M12288', 'BaseEnvironmentAudit.lean'], cwd=scratch, compressed=True)
    rows, metadata = parse_audit(raw)
    validate_import_coverage(metadata, mods | {'NSP14'})
    validate_audit(rows, mods)
    (out / 'base_declarations.json.gz').write_bytes(gzip.compress(json.dumps(rows, ensure_ascii=False, indent=2).encode(), mtime=0))
    write_json(out / 'base_environment.json', {'base_commit': BASE, 'isolated_workspace': str(scratch),
               'cache_donor': cache_donor, 'shared_packages': str((root / '.lake/packages').resolve()),
               'source_identity_checked': True, 'declarations': len(rows)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir')
    parser.add_argument('--fresh-project-cache', action='store_true')
    parser.add_argument('--baseline-cache')
    parser.add_argument('--preflight', action='store_true')
    args = parser.parse_args()
    created_out = False
    try:
        validate_changes(ROOT, require_new=not args.preflight)
        if args.preflight:
            print('PASS_V06_PREFLIGHT (not certification)')
            return
        if not args.fresh_project_cache:
            raise ValueError('--fresh-project-cache is required for complete verification')
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        rel = args.output_dir or f'verification/run18/runs/v06_alignment_{stamp}_{uuid.uuid4().hex[:8]}'
        out = validate_output(ROOT, rel)
        proof = git(ROOT, 'rev-parse', 'HEAD').decode().strip()
        subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, proof], cwd=ROOT, check=True)
        initial = source_manifest(ROOT)
        check_source_manifest(ROOT, initial, proof)
        retained = preserve_evidence(ROOT, out)
        prior = json.loads((ROOT / R16 / 'verification.json').read_text())
        if len(prior['checks']) != 280 or len(prior['fixture_order']) != 268:
            raise ValueError('fixed R16 replay inventory differs')
        out.mkdir(parents=True, exist_ok=False)
        created_out = True
        print('EVIDENCE_DIRECTORY', rel, flush=True)
        write_json(out / 'SOURCE_SHA256.json', initial)
        write_json(out / 'INHERITED_EVIDENCE_SHA256.json', retained)
        write_json(out / 'change_policy.json', {'base': BASE, 'modified': sorted(MODIFIED),
                   'append_only': sorted(APPEND_ONLY), 'new': sorted(NEW_FILES)})
        snapshot = {'proof_snapshot_commit': proof, 'baseline_commit': BASE,
                    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
                    'mathlib_commit': git(ROOT / '.lake/packages/mathlib', 'rev-parse', 'HEAD').decode().strip(),
                    'fixture_threads': 1, 'fixture_memory_limit_mib': 12288}
        if 'version 4.36.0-rc2,' not in snapshot['lean_version'] or snapshot['mathlib_commit'] != MATHLIB:
            raise ValueError('toolchain or mathlib pin mismatch')
        write_json(out / 'snapshot.json', snapshot)
        records = []
        def invariant():
            if git(ROOT, 'rev-parse', 'HEAD').decode().strip() != proof:
                raise ValueError('HEAD changed during verification')
            check_source_manifest(ROOT, initial)
        def run(name, command, cwd=ROOT, compressed=False, expected=None):
            invariant()
            start = time.monotonic()
            result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            data = result.stdout.encode()
            (out / (name + ('.log.gz' if compressed else '.log'))).write_bytes(gzip.compress(data, mtime=0) if compressed else data)
            ok = (result.returncode == 0 and not re.search(r'\bwarning:', result.stdout)) if expected is None else (
                result.returncode == 1 and expected in result.stdout and 'lean.unknownIdentifier' in result.stdout and 'does not exist' not in result.stdout)
            records.append({'name': name, 'command': command, 'cwd': str(cwd), 'exit_code': result.returncode,
                            'expected_missing_declaration': expected, 'passed': ok, 'seconds': round(time.monotonic() - start, 3)})
            write_json(out / 'checks.in_progress.json', records)
            print(name, result.returncode, 'PASS' if ok else 'FAIL', flush=True)
            invariant()
            if not ok:
                raise ValueError('check failed: ' + name)
            return result.stdout
        backup = Path(tempfile.mkdtemp(prefix='nsp14-v06-cold-cache-'))
        moved = []
        for name in ['.lake/build/lib/lean', '.lake/build/ir']:
            source = ROOT / name
            if source.exists():
                target = backup / name.replace('/', '_')
                shutil.move(str(source), str(target))
                moved.append({'from': name, 'to': str(target)})
        write_json(out / 'fresh_cache.json', {'whole_project_lib_and_ir': True, 'moved': moved,
                   'shared_mathlib_cache_untouched': True})
        ordered = fixture_order(ROOT, prior['fixture_order'] + sorted(NEW_FIXTURES))
        (out / 'EnvironmentAudit.lean').write_text(audit_source(['NSP14'] + [p[:-5].replace('/', '.') for p in ordered], AUDITED_MODULES))
        mapping = []
        # Preserve all 280 command identities. Existing output paths and generated
        # audit input are explicitly mapped into this newly-created evidence run.
        for old in prior['checks']:
            new = [arg.replace(R16 + '/', rel + '/') for arg in old['command']]
            mapping.append({'name': old['name'], 'old_command': old['command'], 'new_command': new})
        write_json(out / 'COMMAND_MAP.json', mapping)
        by_name = {row['name']: row for row in mapping}
        raw_environment = None
        for old in prior['checks']:
            if old['name'].startswith('fixture_'):
                continue
            if old['name'] == 'build':
                run(old['name'], by_name[old['name']]['new_command'])
                for index, name in enumerate(ordered):
                    target = Path('.lake/build/lib/lean') / Path(name).with_suffix('.olean')
                    (ROOT / target).parent.mkdir(parents=True, exist_ok=True)
                    # Keep old command/name exactly; extra fixtures have new names.
                    old_fixture = next((c for c in prior['checks'] if c['name'].startswith('fixture_') and name in c['command']), None)
                    label = old_fixture['name'] if old_fixture else 'v06_fixture_' + str(index).zfill(3) + '_' + Path(name).stem
                    command = by_name[label]['new_command'] if old_fixture else ['lake', 'env', 'lean', '-j1', '-M12288', name, '-o', str(target)]
                    run(label, command)
                continue
            raw = run(old['name'], by_name[old['name']]['new_command'], expected=old.get('expected_missing_declaration'), compressed=old['name'] == 'environment_axioms')
            if old['name'] == 'environment_axioms':
                raw_environment = raw
        run('v06_routes', ['python3', 'scripts/check_v06_routes.py', '--output', str(Path(rel) / 'routes.json')])
        run('v06_alignment_controls', ['python3', 'scripts/check_v06_alignment_controls.py', '--output', str(Path(rel) / 'alignment_controls.json')])
        base_rows = baseline_audit(ROOT, out, run, args.baseline_cache)
        rows, metadata = parse_audit(raw_environment)
        validate_import_coverage(metadata, AUDITED_MODULES | IMPORT_ONLY_MODULES)
        write_json(out / 'environment_import_coverage.json', metadata)
        validate_audit(rows, AUDITED_MODULES, base_rows)
        for row in rows:
            name = row['module'].replace('.', '/') + '.lean'
            row['source'] = name
            row['source_sha256'] = initial[name]
            row['exported_kind'] = row['kind']
            if row['kind'] == 'axiom':
                row['kind'] = 'exported_proof_stub'
        (out / 'declarations.json.gz').write_bytes(gzip.compress(json.dumps(sorted(rows, key=lambda r: r['name']), ensure_ascii=False, indent=2).encode(), mtime=0))
        write_json(out / 'audit_coverage.json', {'typed_modules': sorted(AUDITED_MODULES),
                   'verified_import_only_modules': sorted(IMPORT_ONLY_MODULES),
                   'base_export_modules': sorted({r['module'] for r in base_rows}),
                   'normal_and_explicit_types': True, 'all_project_transitive_axioms': True,
                   'base_public_exports_compared': sum(not r['name'].startswith('_private.') for r in base_rows),
                   'module_declaration_counts': {m: sum(r['module'] == m for r in rows) for m in sorted(AUDITED_MODULES)}})
        invariant()
        validate_changes(ROOT)
        if preserve_evidence(ROOT, out) != retained:
            raise ValueError('inherited evidence bytes or fileset changed')
        if {r['name'] for r in prior['checks']} - {r['name'] for r in records}:
            raise ValueError('R16 command replay coverage missing')
        summary = {'status': 'V06_ALIGNMENT_COMPLETE', 'v06_alignment_complete': True,
                   'scope': SCOPE, 'baseline_commit': BASE, 'proof_snapshot_commit': proof,
                   'evidence_directory': rel, 'inherited_run18_complete_preserved': True,
                   'inherited_replay': R16, 'inherited_command_count': 280,
                   'fixture_order': ordered, 'fixture_count': len(ordered), 'checks': records,
                   'fresh_whole_project_cache': True, 'base_public_types_preserved': True,
                   'normal_explicit_type_and_axiom_coverage': sorted(AUDITED_MODULES),
                   'verified_import_only_modules': sorted(IMPORT_ONLY_MODULES),
                   'allowed_axioms': sorted(ALLOWED_AXIOMS), 'environment_declarations': len(rows),
                   'preserved_evidence_count': len(retained), 'frozen_requested_goals_sha256': FROZEN,
                   'not_claimed': ['N4', 'Run19', 'all_P14']}
        write_json(out / 'verification.json', summary)
        write_json(out / 'MANIFEST_SHA256.json', evidence_manifest(ROOT, out))
        print(summary['status'], len(records), 'checks', len(rows), 'declarations', flush=True)
    except (ValueError, OSError, subprocess.CalledProcessError, KeyError) as exc:
        if created_out:
            write_json(out / 'failure.json', {'status': 'FAILED_V06_ALIGNMENT_ATTEMPT', 'error': str(exc),
                       'proof_snapshot_commit': locals().get('proof'), 'checks': locals().get('records', [])})
        parser.exit(1, str(exc) + '\n')


if __name__ == '__main__':
    main()
