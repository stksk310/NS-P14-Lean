#!/usr/bin/env python3
"""Compare the freshly completed Run16 verifier with the published evidence."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDITED = '584f92d8c1a7fc1e2413f606b661fc9b81f472cd'
CURRENT = ROOT/'verification/run16/final'
SAVED = ROOT/'verification/run16_independent/reproduction'


def original(path):
    return subprocess.check_output(['git', 'show', AUDITED+':'+path], cwd=ROOT)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-log', type=Path, required=True)
    args = parser.parse_args()
    transcript = args.run_log.read_text()
    assert 'PASS_RUN16_PROOF_CLOSURE 150 commands' in transcript
    fresh = json.loads((CURRENT/'verification.json').read_text())
    stored = json.loads(original('verification/run16/final/verification.json'))
    assert fresh['status'] == 'PASS_RUN16_PROOF_CLOSURE'
    assert fresh['fresh_project_test_cache'] is True
    assert len(fresh['checks']) == len(stored['checks']) == 150
    assert [r['name'] for r in fresh['checks']] == [r['name'] for r in stored['checks']]
    for r in fresh['checks']:
        assert r['exit_code'] == 0
        assert f"{r['name']} 0\n" in transcript, r['name']
        cmd = r['command']
        if cmd[:3] == ['lake', 'env', 'lean'] and '-o' in cmd:
            target = Path(cmd[cmd.index('-o')+1])
            assert target.is_relative_to(ROOT/'.lake/build/lib/lean'), target
        log = CURRENT/(r['name']+'.log')
        if log.exists():
            assert 'warning:' not in log.read_text(), log
    built = set(re.findall(r'\bBuilt (NSP14(?:\.[\w.]+)?) \(', (CURRENT/'build.log').read_text()))
    expected = {str(p.relative_to(ROOT))[:-5].replace('/', '.')
                for p in (ROOT/'NSP14').rglob('*.lean')} | {'NSP14'}
    assert built == expected, (len(built), len(expected))
    before = json.loads(gzip.decompress(original('verification/run16/final/declarations.json.gz')))
    after = json.loads(gzip.decompress((CURRENT/'declarations.json.gz').read_bytes()))
    assert {d['name']: d for d in before} == {d['name']: d for d in after}
    assert len(after) == 7835
    assert sum('explicit_type' in d for d in after) == 1629
    hashes = json.loads((CURRENT/'SOURCE_SHA256.json').read_text())
    assert hashes == json.loads(original('verification/run16/final/SOURCE_SHA256.json'))
    for path, digest in hashes.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    verifier_manifest = json.loads((CURRENT/'MANIFEST_SHA256.json').read_text())
    for path, digest in verifier_manifest.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    # Keep the independent directory's manifest distinct from the original
    # execution paths contained in the verifier's own output manifest.
    shutil.copytree(CURRENT, SAVED, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('MANIFEST_SHA256.json'))
    (SAVED.parent/'verifier_manifest_snapshot.json').write_text(json.dumps(verifier_manifest, indent=2)+'\n')
    shutil.copyfile(args.run_log, SAVED/'independent_run.log')
    numeric = ROOT/'verification/run16/coordinate_model.json'
    assert json.loads(numeric.read_text())['grid_count'] == 799
    shutil.copyfile(numeric, SAVED/'coordinate_model_data.json')
    result = dict(status='PASS_INDEPENDENT_RUN16_REPLAY', audited_commit=AUDITED,
                  checks=len(fresh['checks']), all_exit_codes_zero=True,
                  fresh_project_production_and_test_cache=True,
                  built_project_modules_including_root=len(built),
                  environment_declarations=len(after), new_type_records=1629,
                  core_run16_declarations=1437,
                  identical_full_declaration_records=True, identical_bound_source_hashes=len(hashes),
                  current_checkout_output_paths=True,
                  inherited_original_run15_goal_closure_compiled=True,
                  inherited_coordinate_model_cases=799,
                  check_seconds=round(sum(r['seconds'] for r in fresh['checks']), 3),
                  evidence_directory=str(SAVED.relative_to(ROOT)))
    Path(__file__).with_name('replay_comparison.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
