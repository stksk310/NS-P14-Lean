#!/usr/bin/env python3
"""Read-only Git-byte/manifest validation of the adopted Run19 and V06 inputs."""
from pathlib import Path
import hashlib,json,subprocess,zipfile

ROOT=Path(__file__).resolve().parents[3]
BASE='07fe1ed952ae31ce01255ce53df538bf0a76d5cc'
PROOF='7c6821ee0f43869b2a9b5d9b1b72b8d7a045b4a7'
EVIDENCE='c12fbfa66fb7585af013b8bcc4da4fa7ca34fdbe'
REVIEW='1533762c276df346350a382ba452d73a5ae219ad'
UPSTREAM_AUDIT='342fbdda072fc5d6aa5e8f2d8968456cc54c12a6'
RUN='verification/run19/runs/release_20261116_r03'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(ref,name):return subprocess.check_output(['git','show',ref+':'+name],cwd=ROOT)

def main():
    complete=json.loads((ROOT/'verification/run19/RUN19_COMPLETE_20261116_R03.json').read_text())
    assert complete['status']=='RUN19_COMPLETE' and complete['run19_complete'] and not complete['all_P14_complete']
    out=ROOT/RUN;summary=json.loads((out/'verification.json').read_text())
    assert len(summary['checks'])==318 and len(summary['fixture_order'])==299 and all(c['passed'] for c in summary['checks'])
    assert not summary['unproved_ids'] and len(summary['closed_ids'])==10 and summary['proof_snapshot_commit']==PROOF
    source=json.loads((out/'SOURCE_SHA256.json').read_text())
    append_only={'NSP14.lean','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md'}
    adopted=set(subprocess.check_output(['git','diff','--name-only',BASE,UPSTREAM_AUDIT],cwd=ROOT,text=True).splitlines())
    for n in adopted:assert (ROOT/n).read_bytes()==blob(UPSTREAM_AUDIT,n),n
    for n,h in source.items():
        old=blob(PROOF,n);assert sha(old)==h,n
        now=(ROOT/n).read_bytes()
        assert (now.startswith(old) if n in append_only else now==blob(UPSTREAM_AUDIT,n) if n in adopted else sha(now)==h),n
    manifest=json.loads((out/'MANIFEST_SHA256.json').read_text())
    actual={str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in out.rglob('*') if p.is_file() and p.name!='MANIFEST_SHA256.json'}
    assert actual==manifest
    for n in list(manifest)+[RUN+'/MANIFEST_SHA256.json']:
        assert (ROOT/n).read_bytes()==blob(EVIDENCE,n),n
    retained=json.loads((out/'INHERITED_EVIDENCE_SHA256.json').read_text())
    for n,h in retained.items():assert sha((ROOT/n).read_bytes())==h,n
    rp='verification/run19/review/final_20261116_r03.json';review=json.loads((ROOT/rp).read_text())
    assert review['verdict']=='PASS' and all(review[k]==0 for k in ['critical','important','minor'])
    assert review['pending']==review['declined']==[] and review['reviewed_commit']==EVIDENCE and review['source_snapshot_commit']==PROOF
    assert review['verification_summary_sha256']==sha((out/'verification.json').read_bytes())
    assert review['verification_manifest_sha256']==sha((out/'MANIFEST_SHA256.json').read_bytes())
    assert sha((ROOT/review['review_report']).read_bytes())==review['review_report_sha256']
    for n in [rp,review['review_report']]:assert blob(REVIEW,n)==(ROOT/n).read_bytes()
    archive=ROOT/complete['archive'];assert sha(archive.read_bytes())==complete['archive_sha256']
    assert blob(complete['normal_push']['pushed_package_commit'],complete['archive'])==archive.read_bytes()
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None and len(z.namelist())==len(set(z.namelist()))==1959
        bundle=json.loads(z.read('BUNDLE_SHA256.json'))
        assert set(z.namelist())==set(bundle)|{'BUNDLE_SHA256.json'}
        for n,h in bundle.items():
            assert not Path(n).is_absolute() and '..' not in Path(n).parts
            assert sha(z.read(n))==h
        binding=json.loads(z.read('RUN19_BINDING.json'))
        assert binding['proof_snapshot_commit']==PROOF and binding['reviewed_evidence_commit']==EVIDENCE and binding['review_commit']==REVIEW
        assert sha(z.read(review['review_report']))==review['review_report_sha256']
    frozen=json.loads((ROOT/'verification/run19/sources/initial_contracts_20261116/FROZEN_SHA256.json').read_text())
    for n,h in frozen.items():assert sha((ROOT/n).read_bytes())==h
    expected={'proof_sharp_v6/NS_P14_SHARP_PROOF_JA.md':'fe8271bbaabf6b3d31243628c3a5a5a305b82361c794f03c6e13a2fe98c72791',
              'proof_sharp_v6/chapters/06_SYNTHESIS_JA.md':'67a10b00ab51ab1836fc071bb1c03b9fa2898ec470e84762151aeba032316f4d'}
    for n,h in expected.items():assert sha((ROOT/n).read_bytes())==h
    prior=ROOT/'verification/run18/runs/v06_alignment_20261115T152000Z_r01'
    v=json.loads((prior/'verification.json').read_text());assert len(v['checks'])==289 and len(v['fixture_order'])==273
    for n,h in json.loads((prior/'MANIFEST_SHA256.json').read_text()).items():assert sha((ROOT/n).read_bytes())==h
    integration=json.loads((ROOT/'verification/run18/runs/v06_alignment_integration_20261116_r01/receipt.json').read_text())
    assert integration['certified_proof_commit']=='d446fc2f18f7a8603d1eedd446e93810dc44d01c' and integration['no_lean_test_verifier_or_pin_changes']
    print(json.dumps({'status':'PASS_ADOPTED_RUN19_V06_BINDINGS_NOT_RUN20_CERTIFICATION','adopted_base':BASE,'proof':PROOF,'evidence':EVIDENCE,'review':REVIEW,
       'source_files':len(source),'evidence_files':len(manifest),'preserved_prior_files':len(retained),'checks':318,'fixtures':299,
       'all_frozen_ten_contract_files':len(frozen),'archive_entries':1959,'manuscript_hashes':expected,'v06_checks':289,'v06_fixtures':273},indent=2))
if __name__=='__main__':main()
