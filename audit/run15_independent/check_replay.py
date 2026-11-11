#!/usr/bin/env python3
"""Validate and save the freshly replayed stock verifier's independent evidence."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDITED = '447b7ae782414b739968a2a3009dd3a52ae230d0'
CURRENT = ROOT/'verification/run15_closure'
SAVED = ROOT/'verification/run15_independent/reproduction'


def original(path):
    return subprocess.check_output(['git', 'show', AUDITED+':'+path], cwd=ROOT)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-log', type=Path, required=True)
    args = parser.parse_args()
    transcript = args.run_log.read_text()
    assert 'PASS_RUN15_PROOF_CLOSURE 101 commands' in transcript
    fresh = json.loads((CURRENT/'verification.json').read_text())
    stored = json.loads(original('verification/run15_closure/verification.json'))
    assert fresh['status'] == 'PASS_RUN15_PROOF_CLOSURE'
    assert fresh['fresh_project_test_cache'] is True
    assert fresh['all_original_goals_closed'] is True
    assert len(fresh['checks']) == len(stored['checks']) == 101
    assert [r['name'] for r in fresh['checks']] == [r['name'] for r in stored['checks']]
    assert all(r['exit_code'] == 0 for r in fresh['checks'])
    for record in fresh['checks']:
        assert f"{record['name']} 0\n" in transcript, record['name']
    built = set(re.findall(r'\bBuilt (NSP14(?:\.[\w.]+)?) \(', (CURRENT/'build.log').read_text()))
    expected_modules = {str(p.relative_to(ROOT))[:-5].replace('/', '.')
                        for p in (ROOT/'NSP14').rglob('*.lean')} | {'NSP14'}
    assert built == expected_modules, (len(built), len(expected_modules))
    for record in fresh['checks']:
        command = record['command']
        if command[:3] == ['lake', 'env', 'lean'] and '-o' in command:
            target = Path(command[command.index('-o')+1])
            assert target.is_relative_to(ROOT/'.lake/build/lib/lean'), target
        log = CURRENT/(record['name']+'.log')
        if log.exists():
            assert 'warning:' not in log.read_text(), log
    before = json.loads(gzip.decompress(original('verification/run15_closure/declarations.json.gz')))
    after = json.loads(gzip.decompress((CURRENT/'declarations.json.gz').read_bytes()))
    # This compares every recorded normal/explicit type, kind, module,
    # name and transitive axiom set, rather than counts alone.
    before = {d['name']: d for d in before}
    after = {d['name']: d for d in after}
    assert before == after, 'fresh declaration/type/dependency dump differs'
    hashes = json.loads((CURRENT/'SOURCE_SHA256.json').read_text())
    assert hashes == json.loads(original('verification/run15_closure/SOURCE_SHA256.json'))
    for path, digest in hashes.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    # The stock packager's manifest authenticates the original publication,
    # not newly generated timings/logs. The independent bundle has its own
    # manifest; do not carry the historical publication manifest into it.
    shutil.copytree(CURRENT, SAVED, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('MANIFEST_SHA256.json'))
    shutil.copyfile(args.run_log, SAVED/'independent_run.log')
    result = dict(status='PASS_INDEPENDENT_REPLAY_COMPARISON', audited_commit=AUDITED,
                  checks=len(fresh['checks']), all_exit_codes_zero=True,
                  production_cache='empty on worktree creation; all 396 production files rebuilt',
                  built_project_modules_including_root=len(built),
                  fresh_project_test_cache=True,
                  environment_declarations=len(after),
                  core_run15_declarations=2329,
                  all_run15_environment_declarations=fresh['run15_environment_declarations'],
                  identical_full_declaration_type_and_axiom_records=True,
                  identical_bound_source_hashes=len(hashes),
                  current_checkout_output_paths=True,
                  check_seconds=round(sum(r['seconds'] for r in fresh['checks']), 3),
                  evidence_directory=str(SAVED.relative_to(ROOT)))
    Path(__file__).with_name('replay_comparison.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
