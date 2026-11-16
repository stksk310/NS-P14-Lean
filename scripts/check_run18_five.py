#!/usr/bin/env python3
"""Independent finite checks of actual five-generator cores; Lean supplies universal proofs."""
from itertools import combinations
from math import comb,gcd
from pathlib import Path
import argparse,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
def C(n,k):return comb(n,k)if 0<=k<=n else 0
def minimal_points(a,u):
    sums={0};points={(0,0)}
    for n in range(1,u):
        nxt={b+c for b in [0,*a,u]for c in sums}
        points.update((n,b)for b in nxt if b not in sums and b-u not in sums)
        sums=nxt
    return points
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);args=p.parse_args()
    rel=Path(args.output)
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:3]!=('verification','run18','runs'):p.error('new output under verification/run18/runs required')
    out=ROOT/rel
    if out.exists():p.error('existing evidence is immutable')
    spec=importlib.util.spec_from_file_location('coordinates',ROOT/'scripts/check_run16_coordinates.py')
    model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    records=[];presentations=[]
    for a in combinations(range(1,5),3):
        r=model.check(17,3,list(a),5,matrices=True)
        assert r['R']==0 and r['Hx']<=1 and r['PC']<=6
        for characteristic,b in r['QC_Betti_by_characteristic'].items():
            assert b[2]+1==b[1]+b[3]
            if a in [(1,2,4),(1,3,4)]:assert b[1]<=5 and b[3]+3<=r['PC']
            else:assert r['PC']<=5 and b[1]<=6 and b[3]+1<=r['PC']
            assert b[1]+r['PC']<=11 and b[2]+3*r['PC']<=25
            for i in range(1,6):
                cap=(b[i]if i<len(b)else 0)+r['PC']*C(3,i-1)
                assert cap<=i*C(5,i+1)+min(C(5,i-1),C(5,i))
        if a in [(1,2,4),(1,3,4)]:
            x,y,z=(4,1,2)if a==(1,2,4)else(1,3,4)
            actual=minimal_points(a,5)
            assert actual=={(0,0),(1,x),(1,y),(1,z),(2,2*x),(2,y+z)}
            # The selected three row/column entries of the actual d3 are diagonal units.
            rows=[(x,(1,x)),(x,(2,2*x)),(z,(2,y+z))]
            columns=[(0,0),(1,x),(1,y)]
            minor=[[int((n+1,B+var)==point)for n,B in columns]for var,point in rows]
            assert minor==[[1,0,0],[0,1,0],[0,0,1]]
        records.append(r)
    for h,t in [(4,1),(4,3),(5,2),(6,1),(7,2)]:
        u=2*h;a=[t,h,t+h]
        m=3*u+2
        r=model.check(m,3,a,u,matrices=True)
        actual=minimal_points(a,u)
        standard={(n,n*t+j*h)for n in range(h)for j in range(n+1)}|{(1,h)}
        assert actual==standard and len(actual)==C(h+1,2)+1
        assert r['PC']==C(h+1,2)+1 and r['W']==h*h-h+2
        for b in r['QC_Betti_by_characteristic'].values():
            assert b[1]==h+4 # finite check only; not claimed as a universal Lean export
            assert b[1]+r['PC']+r['R']<=C(u,2)+1
        for y in range(h+2):
            for z in range(h+2):
                for w in range(h+2):
                    killed=(y*z>0 or z>=2 or z*w>0 or y+w>=h)
                    normal=(z==1 and y==w==0)or(z==0 and y+w<h)
                    assert killed!=normal
        presentations.append(dict(h=h,t=t,coprime_mod_h=gcd(t,h)==1,unit_mod_u=gcd(t,u)==1,
            actual_basis=sorted(actual),literal_ideal='(YZ,Z^2,ZW)+(Y,W)^h'))
        records.append(r)
    result=dict(status='PASS_FINITE_FIVE_CHECKS_NOT_UNIVERSAL_PROOF',actual_core_examples=records,
        presentations=presentations,closed_universal_Lean_contract='NSP14.Run18.five_closed',
        note='Each characteristic 0/2/3 rank is computed independently. Exact antipodal b1=h+4 is checked only on these fixtures; universal comparison uses the proved P bound instead. Run18 remains PARTIAL.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],len(records),'actual cores',len(presentations),'presentations')
if __name__=='__main__':main()
