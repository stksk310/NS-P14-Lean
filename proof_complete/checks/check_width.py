"""Exact polynomial-identity checks for the paper W-tail, using only Fraction.

The two cleared identities have degree <=3 in v and <=2 in z; a 4x3 grid
therefore determines them. The universal bounds are proved in the manuscript.
"""
from fractions import Fraction as Q
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    checks=0
    for h in (0,1):
        for v in range(4):
            for z in range(3):
                s=v+4; e=2*s+1-h; u=2*e-2+z; delta=u-(e-1)
                bcap=u+Q(delta**2,2*s)+Q(delta,2)+Q(s,8)
                gap=Q(u*(u-1),2)+1-(Q(e+3,3)*bcap-u+Q(e*(e-1),6))
                expected=(62*v**3+40*v*v*z+(556-47*h)*v*v+4*v*z*z
                          +(220-4*h)*v*z+(1496-252*h)*v+4*h*z*z
                          +(240+8*h)*z+1056-268*h)
                need(24*s*gap==expected,(h,v,z,'first-row identity'))
                checks+=1
    for e in range(5,10):
        for z in range(4):
            u=2*e-2+z; v=e-8
            need(2*u*u-(3*e+6)*u+6*e-2==
                 2*v*v+5*v*z+16*v+2*z*z+26*z+18,'second-row identity')
    for u in range(10,14):
        need(Q(u,6)*(2*u*u-24*u+34)+10==Q((u-10)*(u-3)*(u+1),3),
             'e6 factorization')
    need(3*17-10+5==46,'e6 boundary')
    need((5*13)//2-8+5==29,'e5 non-antipodal u8 boundary')
    print(json.dumps({'status':'PASS_EXACT_WIDTH_IDENTITIES',
                      'two_variable_identity_grid_points':checks,
                      'scope':'Polynomial identities and explicit small boundaries; no source sampling or Lean verification.'}))


if __name__=='__main__':main()
