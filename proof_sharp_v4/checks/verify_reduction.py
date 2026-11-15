#!/usr/bin/env python3
"""Exact transcription/coverage checks. These checks do not prove universality."""
from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import re
import subprocess
import sympy as sy

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "proof_sharp_v4"
BASE = "345e2d82fea50ef89e00a8f35c4fb53ac601d7ce"


def C(n, i):
    return comb(n, i) if 0 <= i <= n else 0


def cap(v, D, i):
    if i == 0:
        return 1
    if i > v:
        return 0
    return i*C(v, i+1) + ((D+1-i)*C(v, i-1) if i <= D else (i-D)*C(v, i))


def capmin(v, i):
    return 1 if i == 0 else 0 if i > v else i*C(v, i+1)+min(C(v, i-1), C(v, i))


def main():
    identities = []
    h, z, u, e, v, t = sy.symbols("h z u e v t")
    Q = sy.Rational

    def identity(name, left, right):
        assert sy.cancel(left-right) == 0, name
        identities.append(name)

    U2 = Q(5, 4)*u*u-2*u+4
    U3 = u*u-3*u+4
    U4 = Q(1, 4)*u*u-u+1
    T2 = u*(u-1)*(u-2)/3
    identity("N4 cubic for every u=6+z", (12*(T2-U2)).subs(u, 6+z),
             4*z**3+45*z**2+140*z+36)
    identity("N4 third-row comparison", U2-U3, u*u/4+u)
    identity("N4 fourth-row comparison", U2-5*U4, 3*u-1)
    A = h*(2*h-1)+1
    B = (11*h*h-7*h+30)/6
    identity("APD integer capacity plus one", A+1-B, (h*h+h-18)/6)
    identity("APD positive polynomial from h=4", (h*h+h-18).subs(h, 4+z), z*z+9*z+2)
    identity("sparse second-row polynomial", (2*u*u-(3*e+6)*u+6*e-2).subs(u, 2*e-2+z).subs(e, 7+v),
             2*v*v+5*v*z+12*v+2*z*z+21*z+4)
    identity("five higher second row", (T2-(Q(5, 2)*u*u-4*u-4)).subs(u, 9+z),
             (2*z**3+33*z*z+136*z+33)/6)
    identity("dense positive gap", (5*t*t-17*t-6+6*(t-1)*v).subs(t, 4+z),
             5*z*z+23*z+6+6*z*v+18*v)
    identity("sparse e6 endpoint factor", u*(2*u*u-24*u+34)/6+10,
             (u-10)*(u-3)*(u+1)/3)
    bstar = {
        6: (u*u-u+12)/6, 7: (u*u-3*u+20)/6,
        8: (u*u-2*u+25)/8, 9: (u*u-4*u+36)/8,
    }
    firstgap = {
        6: z*z/24+Q(43, 24)*z+Q(1, 2), 7: 2*z+1,
        8: Q(3, 32)*z*z+Q(63, 16)*z+Q(211, 32),
        9: z*z/16+Q(17, 4)*z+Q(29, 4),
    }
    for en in bstar:
        old_bound = Q(en+5, 4)*bstar[en]-u+Q((en-1)*en*(en+1), 24)
        identity(f"sparse first row e={en}", (u*(u-1)/2+1-old_bound).subs(u, 2*en-2+z), firstgap[en])

    finite = 0
    for vn in range(1, 101):
        for i in range(0, vn+3):
            assert min(cap(vn, D, i) for D in range(1, vn+1)) == capmin(vn, i)
            finite += 1
            if 1 <= i <= vn:
                assert capmin(vn+1, i) >= capmin(vn, i)
                finite += 1
    assert [capmin(4, i) for i in [2, 3, 4]] == [12, 7, 1]
    assert [capmin(5, i) for i in [2, 3, 4]] == [25, 25, 9]
    assert [capmin(6, i) for i in [2, 3, 4, 5]] == [46, 60, 39, 11]
    assert [capmin(7, i) for i in [2, 3, 4, 5]] == [77, 126, 119, 56]
    for hn in range(4, 1001):
        an = hn*(2*hn-1)+1
        bn = Fraction(11*hn*hn-7*hn+30, 6)
        assert bn < an+1 and bn.numerator//bn.denominator <= an
        finite += 1
    for un in range(6, 501):
        bounds = [Fraction(5, 4)*un*un-2*un+4,
                  un*un-3*un+4, Fraction(un*un, 4)-un+1]
        for i, bound in zip([2, 3, 4], bounds):
            assert bound <= i*C(un, i+1)
            finite += 1

    # Check the interval partition, not realizability or universality of semigroups.
    partitions = 0
    for en in range(4, 41):
        for un in range(en-1, 201):
            if en == 4:
                first = [un in [3, 4], un == 5, un in [6, 7, 8], un >= 9]
                higher = [un == 3, un == 4, un == 5, un >= 6]
                assert sum(first) == sum(higher) == 1
            elif en == 5:
                assert sum([un == 4, un == 5, un in [6, 7], un >= 8]) == 1
            else:
                assert sum([un == en-1, un == en, en+1 <= un <= 2*en-3, un >= 2*en-2]) == 1
            partitions += 1

    ordinary = subprocess.run(["python3", "-B", str(OUT / "checks/check_ordinary_identities.py")],
                              cwd=ROOT, capture_output=True, text=True)
    (OUT / "build/ordinary_transcription.log").write_text(ordinary.stdout+ordinary.stderr)
    assert ordinary.returncode == 0

    # Original tracked files, including proof, production, fixtures and old evidence.
    tracked = subprocess.run(["git", "diff", "--exit-code", BASE, "--"], cwd=ROOT,
                             capture_output=True, text=True)
    assert tracked.returncode == 0, "An original tracked file changed: " + tracked.stdout[:1000]
    chapters = sorted((OUT / "chapters").glob("*.md"))
    canonical = (OUT / "NS_P14_SHARP_PROOF_JA.md").read_text()
    for chapter in chapters:
        text = chapter.read_text()
        assert text in canonical, f"Stale canonical chapter {chapter.name}"
        for opening, closing in [(r"\(", r"\)"), (r"\[", r"\]")]:
            assert text.count(opening) == text.count(closing), chapter.name
        assert not re.search(r"TODO|TBD|FIXME|PLACEHOLDER", text), chapter.name

    status = json.loads((ROOT / "docs/RUN18_CLOSURE_STATUS.json").read_text())
    release = ROOT / "verification/run18/runs/release_candidate_20261115_r16"
    counts = {}
    for name in ["SOURCE_SHA256.json", "MANIFEST_SHA256.json"]:
        manifest = json.loads((release/name).read_text())
        for name0, expected in manifest.items():
            assert sha256((ROOT/name0).read_bytes()).hexdigest() == expected, name0
        counts[name] = len(manifest)
    evidence = json.loads((release / "verification.json").read_text())
    assert status["run18_complete"] and not status["unproved_ids"]
    assert all(c["passed"] for c in evidence["checks"])
    pagination = json.loads((OUT / "PAGINATION.json").read_text())
    assert pagination["outputs"][0]["missing_character_warnings"] == 0
    assert pagination["outputs"][0]["overfull_boxes"] == 0
    snapshot = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
                for p in sorted(OUT.rglob("*.md"))}
    result = {
        "status": "PASS_PAPER_REDUCTION_TRANSCRIPTION_AND_PRESERVATION_CHECKS",
        "base_commit": BASE,
        "symbolic_identities": identities,
        "finite_transcription_checks": finite,
        "partition_sanity_cases": partitions,
        "ordinary_checker": "PASS",
        "all_original_tracked_bytes_unchanged": True,
        "canonical_matches_all_chapters": True,
        "run18_recorded_checks_passed": len(evidence["checks"]),
        "rehashed_existing_manifests": counts,
        "new_lean_build_performed": False,
        "new_lean_formalization_performed": False,
        "external_originals_independently_reread": False,
        "published_input_network_probe": "LTV arxiv request blocked by proxy 403; existing source registrations were read",
        "proof_status": "Complete paper argument citing named published inputs; independent local reviews recorded separately",
        "limitations": ["Symbolic and finite checks detect transcription errors; universal proofs are the mathematical arguments in the manuscript.",
                        "Recorded Run18 kernel evidence was rehashed, not freshly rebuilt.",
                        "The N4/global and new unified paper lemmas are not new Lean certifications."],
        "markdown_sha256": snapshot,
    }
    (OUT / "verification.json").write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ["status", "finite_transcription_checks", "partition_sanity_cases",
                     "run18_recorded_checks_passed", "rehashed_existing_manifests"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
