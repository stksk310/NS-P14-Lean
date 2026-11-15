#!/usr/bin/env python3
"""Exact transcription/coverage checks; universal proofs remain in the manuscript.

Run --math-only while the manuscript and PDFs are being assembled. The default
mode additionally requires the complete current V06 build and frozen V04/V05 files.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import comb, gcd
from pathlib import Path
import json
import re
import subprocess
import sympy as sy

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "proof_sharp_v6"
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


def endpoint_upper(en, un, dimension_bound, i):
    """U_i(B), using zero-extended binomials; valid also beyond the top row."""
    return (dimension_bound*C(en, i)-un*C(en-1, i-1)-C(en-1, i+1))


def normalized_capacity(en, un, i):
    """Only the interval 2<=i<=e is normalized; no division above the top."""
    assert 2 <= en <= un and 2 <= i <= en
    return (Fraction(i*C(un, i+1), C(en, i))
            + Fraction(un*i, en)
            + Fraction((en-i)*(en-i-1), en*(i+1)))


def verify_frozen_version(manifest_name, directory, expected_count):
    """Preserve a previous bundle as a complete file set, not only samples."""
    frozen = json.loads((OUT / manifest_name).read_text())
    assert len(frozen) == expected_count, (directory, len(frozen), expected_count)
    assert all(Path(name).parts[0] == directory for name in frozen)
    previous_files = {str(path.relative_to(ROOT))
                      for path in (ROOT / directory).rglob("*") if path.is_file()}
    assert previous_files == set(frozen), {
        "missing": sorted(set(frozen)-previous_files),
        "unexpected": sorted(previous_files-set(frozen)),
    }
    for name, expected in frozen.items():
        assert sha256((ROOT/name).read_bytes()).hexdigest() == expected, name
    return len(frozen)


def verify_previous_version():
    return verify_frozen_version("PREVIOUS_VERSION_SHA256.json", "proof_sharp_v5", 55)


def verify_ancestor_version():
    return verify_frozen_version("ANCESTOR_V04_SHA256.json", "proof_sharp_v4", 49)


def verify_dependency_guards():
    """Detect accidental loss/reintroduction of the named proof connections.

    These are editorial dependency guards, not checks of mathematical truth.
    The new all-j argument and finite-generation proof are reviewed in prose.
    """
    endpoint = (OUT / "chapters/03_ENDPOINT_JA.md").read_text()
    for label in ["E-5", "E-6", "E-7", "E-8", "E-9", "E-10", "E-11",
                  "E-12", "E-13", "E-TOR"]:
        assert r"\tag{" + label + "}" in endpoint, label
    assert r"\tag{E-STOP}" not in endpoint, "The removed explicit-period lemma returned"
    assert "J_0+p" not in endpoint and "J_0 + p" not in endpoint
    other_chapters = [p for p in (OUT / "chapters").glob("*.md")
                      if p.name != "03_ENDPOINT_JA.md"]
    for chapter in other_chapters:
        assert "E-STOP" not in chapter.read_text(), (
            "A consumer of the deleted stopping lemma returned", chapter.name)
    n4 = (OUT / "chapters/05_N4_JA.md").read_text()
    for label in ["N7b", "N7c", "N7d"]:
        assert r"\tag{" + label + "}" in n4, (
            "Width-four all-competitor argument must remain", label)
    return {"explicit_period_lemma_absent": True,
            "all_j_kernel_resources_and_actual_Tor_labels_retained": True,
            "other_chapters_do_not_reference_removed_lemma": True,
            "width_four_all_competitor_argument_labels_retained": True}


def verify_pagination():
    """Bind every recorded output to the actual PDF, source, pages and log."""
    pagination = json.loads((OUT / "PAGINATION.json").read_text())
    layout = pagination["format"]
    assert layout["font_size_pt"] == 11 and layout["columns"] == 1
    assert layout["margin_mm"] == 25 and layout["paper"] == "A4"
    outputs = pagination["outputs"]
    expected_sources = {
        str((OUT / "NS_P14_SHARP_PROOF_JA.md").relative_to(ROOT)),
        str((OUT / "CURRENT_ROUTE_PAGINATION_REFERENCE_JA.md").relative_to(ROOT)),
    }
    assert len(outputs) == 2
    assert {item["source"] for item in outputs} == expected_sources
    verified = []
    for item in outputs:
        source = ROOT / item["source"]
        pdf = ROOT / item["pdf"]
        tex = ROOT / item["tex"]
        assert source.resolve().is_relative_to(OUT.resolve())
        assert pdf.resolve().is_relative_to((OUT / "build").resolve())
        assert tex.resolve().is_relative_to((OUT / "build").resolve())
        assert pdf.stem == source.stem and pdf.suffix == ".pdf"
        assert tex.stem == source.stem and tex.suffix == ".tex"
        assert sha256(pdf.read_bytes()).hexdigest() == item["sha256"], pdf.name
        assert sha256(source.read_bytes()).hexdigest() == item["source_sha256"], source.name
        assert sha256(tex.read_bytes()).hexdigest() == item["tex_sha256"], tex.name
        assert len(source.read_text()) == item["source_characters"], source.name
        info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                              text=True, check=True).stdout
        pages = re.search(r"^Pages:\s+(\d+)", info, re.M)
        assert pages and int(pages.group(1)) == item["pages"], pdf.name
        assert item["pages"] > 0
        log = pdf.with_suffix(".log").read_text(errors="replace")
        for marker, key in [("Missing character:", "missing_character_warnings"),
                            ("Overfull ", "overfull_boxes")]:
            observed = log.count(marker)
            assert observed == item[key] == 0, (pdf.name, key, observed, item[key])
        assert "Fatal error" not in log and "Emergency stop" not in log, pdf.name
        assert "Output written on" in log, pdf.name
        verified.append({"pdf": item["pdf"], "sha256": item["sha256"],
                         "source": item["source"], "source_sha256": item["source_sha256"],
                         "tex": item["tex"], "tex_sha256": item["tex_sha256"],
                         "pages": item["pages"],
                         "missing_character_warnings": 0, "overfull_boxes": 0})
    return verified


def verify_revision_comparison():
    """Check that the newly recorded V05 comparison names the frozen files."""
    pagination = json.loads((OUT / "PAGINATION.json").read_text())
    assert pagination["revision"] == "V06"
    previous = pagination["previous_revision"]
    assert previous["revision"] == "V05"
    assert previous["source"] == "proof_sharp_v5/NS_P14_SHARP_PROOF_JA.md"
    assert previous["pdf"] == "proof_sharp_v5/build/NS_P14_SHARP_PROOF_JA.pdf"
    source, pdf = ROOT / previous["source"], ROOT / previous["pdf"]
    assert sha256(source.read_bytes()).hexdigest() == previous["source_sha256"]
    assert sha256(pdf.read_bytes()).hexdigest() == previous["sha256"]
    assert len(source.read_text()) == previous["source_characters"]
    info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                          text=True, check=True).stdout
    pages = re.search(r"^Pages:\s+(\d+)", info, re.M)
    assert pages and int(pages.group(1)) == previous["pages"]
    return previous


def main(math_only=False):
    identities = []
    h, z, u, e, v, t = sy.symbols("h z u e v t")
    k, b, i, ratio, dimension, q = sy.symbols("k b i ratio dimension q")
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
    # V05 candidate 1. k=(u-4)//3 and b=(u-4)%3. The identity is
    # polynomial in k,b; only the three possible remainder values are enumerated.
    tail = u+Q(3, 2)*k*(k+1)+(k+1)*b
    identity("V05 nonAP exact step-three tail",
             (6*tail-u*u-u-4-b*(3-b)).subs(u, 3*k+b+4), 0)
    assert [bn*(3-bn) for bn in range(3)] == [0, 2, 2]
    identity("V05 nonAP remainder upper gap", 2-b*(3-b), (b-1)*(b-2))
    first_upper = Q(5, 2)*(u*u+u+6)/6-u+5
    capacity = u*(u-1)/2+1
    identity("V05 nonAP integer capacity plus one",
             capacity+1-first_upper, (u*u+u-66)/12)
    identity("V05 nonAP positive gap from u=8",
             (u*u+u-66).subs(u, 8+z), z*z+17*z+6)
    # V05 candidate 2. Pascal and the two displayed binomial ratios reduce
    # the base, normalized upper, and adjacent increments to these rational
    # identities. The domain i<e is used only for the adjacent ratio.
    base_T = i*(e-i)/(i+1)+i+(e-i)*(e-i-1)/(e*(i+1))
    identity("V05 normalized capacity base", base_T, e-1+i/e)
    normalized_source = (dimension-u*i/e-(e-i)*(e-i-1)/(e*(i+1)))
    normalized_target = ratio+u*i/e+(e-i)*(e-i-1)/(e*(i+1))
    identity("V05 normalized payment equivalence",
             ratio-normalized_source, normalized_target-dimension)
    identity("V05 adjacent normalized binomial ratio",
             (u-i)/(e-i)-1, (u-e)/(e-i))
    identity("V05 adjacent width-increment difference",
             ratio*((i+1)*(u-i)/(e-i)-i)+1/e,
             ratio*(1+(i+1)*(u-e)/(e-i))+1/e)
    identity("sparse second-row polynomial", (2*u*u-(3*e+6)*u+6*e-2).subs(u, 2*e-2+z).subs(e, 7+v),
             2*v*v+5*v*z+12*v+2*z*z+21*z+4)
    identity("five higher second row", (T2-(Q(5, 2)*u*u-4*u-4)).subs(u, 9+z),
             (2*z**3+33*z*z+136*z+33)/6)
    identity("dense positive gap", (5*t*t-17*t-6+6*(t-1)*v).subs(t, 4+z),
             5*z*z+23*z+6+6*z*v+18*v)
    dense_coefficient = (5*t*t-17*t-6)/6+(t-1)*(q-t)
    identity("V06 dense unified nonnegative coefficient",
             6*dense_coefficient,
             12*(q-4)+5*(t-3)**2+(t-3)+6*(t-3)*(q-t))
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

    new_finite = {
        "nonAP_exact_tail_and_integer_slack": 0,
        "normalized_base_step_equivalence_and_monotonicity": 0,
        "normalized_top_row_and_above_top": 0,
        "five_generator_normalized_payment": 0,
    }
    for un in range(8, 1001):
        kn, bn = divmod(un-4, 3)
        exact_tail = un+sum(max(un-4-3*jn, 0) for jn in range(kn+1))
        assert exact_tail == un+3*kn*(kn+1)//2+(kn+1)*bn
        assert 6*exact_tail == un*un+un+4+bn*(3-bn) <= un*un+un+6
        bound = Fraction(5, 2)*Fraction(un*un+un+6, 6)-un+5
        actual_capacity = C(un, 2)+1
        assert bound < actual_capacity+1
        assert bound.numerator//bound.denominator <= actual_capacity
        new_finite["nonAP_exact_tail_and_integer_slack"] += 1

    for en in range(2, 41):
        for un in range(en, 101):
            values = []
            increments = []
            for idx in range(2, en+1):
                value = normalized_capacity(en, un, idx)
                assert normalized_capacity(en, en, idx) == en-1+Fraction(idx, en)
                increment = normalized_capacity(en, un+1, idx)-value
                assert increment == Fraction(idx*C(un, idx), C(en, idx))+Fraction(idx, en)
                # Test the exact equivalence with both an integral and a
                # nonintegral dimension bound; B is an upper bound on P.
                for bn in [Fraction(un*un, max(en-1, 1)), Fraction(un*un+1, 6)]:
                    assert (idx*C(un, idx+1)-endpoint_upper(en, un, bn, idx)
                            == C(en, idx)*(value-bn))
                if idx < en:
                    left = Fraction(C(un, idx+1), C(en, idx+1))
                    right = Fraction(C(un, idx), C(en, idx))*Fraction(un-idx, en-idx)
                    assert left == right
                values.append(value)
                increments.append(increment)
                new_finite["normalized_base_step_equivalence_and_monotonicity"] += 1
            assert values == sorted(values)
            assert increments == sorted(increments)
            assert normalized_capacity(en, un, en) == en*C(un, en+1)+un
            for bn in [Fraction(14), Fraction(un*un, 4)]:
                assert endpoint_upper(en, un, bn, en) == bn-un
                for idx in [en+1, en+2, en+5]:
                    assert endpoint_upper(en, un, bn, idx) == 0
                    try:
                        normalized_capacity(en, un, idx)
                    except AssertionError:
                        pass
                    else:
                        raise AssertionError("Above-top rows must never be normalized")
            new_finite["normalized_top_row_and_above_top"] += 1

    assert normalized_capacity(5, 8, 2) == Fraction(74, 5)
    assert endpoint_upper(5, 8, 14, 2) == 104 <= 2*C(8, 3) == 112
    for un in range(8, 501):
        bn = Fraction(14) if un == 8 else Fraction(un*un, 4)
        assert normalized_capacity(5, un, 2) >= bn
        for idx in range(2, 6):
            assert idx*C(un, idx+1) >= endpoint_upper(5, un, bn, idx)
            assert normalized_capacity(5, un, idx) >= bn
            new_finite["five_generator_normalized_payment"] += 1
    finite += sum(new_finite.values())

    v06_finite = {
        "carry_ceil_and_floor": 0,
        "integer_clamp_height_bound": 0,
        "fixed_target_residue_large_j": 0,
        "dense_unified_all_rows": 0,
        "dense_t2_retained_rows": 0,
    }
    carry_boundaries = {
        "r_zero": False, "s_zero": False, "noncoprime_m_u": False,
        "m_equals_u_plus_one": False, "height_at_most_two": False,
        "height_zero": False, "height_two": False,
    }

    def ceil_div(n, denominator):
        assert denominator > 0
        return -(-n // denominator)

    # The coordinates below smoke-test arithmetic; they are not a finite
    # replacement for the manuscript's all-j kernel or bounded-A argument.
    for un in range(3, 25):
        multiplicities = sorted({un+1, un+2, 2*un-1, 2*un, 2*un+1, 3*un})
        heights = sorted({0, min(1, un-2), min(2, un-2), un-2})
        for mn in multiplicities:
            for jn in sorted({1, 2, 3, un, un+1}):
                for rn in range(un):
                    sn = (rn+jn*mn) % un
                    cn = (rn+jn*mn-sn) // un
                    epsr, epss = int(rn > 0), int(sn > 0)
                    carry = cn-epsr+epss
                    assert epsr == ceil_div(rn, un)
                    assert epss == ceil_div(sn, un)
                    assert carry == ceil_div(rn+jn*mn, un)-ceil_div(rn, un)
                    assert carry >= (jn*mn)//un >= jn
                    v06_finite["carry_ceil_and_floor"] += 1
                    carry_boundaries["r_zero"] |= rn == 0
                    carry_boundaries["s_zero"] |= sn == 0
                    carry_boundaries["noncoprime_m_u"] |= gcd(mn, un) > 1
                    carry_boundaries["m_equals_u_plus_one"] |= mn == un+1
                    for height in heights:
                        for dn in [1, 2, 5]:
                            for ln in sorted({0, height//2, height}):
                                # Evaluate the complete signed integer
                                # expression first, then apply one clamp.
                                start_a = max(0, ln-jn*dn-cn+epsr-epss)
                                assert start_a <= max(0, height-2*jn)
                                v06_finite["integer_clamp_height_bound"] += 1
                                carry_boundaries["height_at_most_two"] |= height <= 2
                                carry_boundaries["height_zero"] |= height == 0
                                carry_boundaries["height_two"] |= height == 2
            for sn in range(un):
                for height in heights:
                    jn = max(1, ceil_div(height, 2))+un
                    rn = (sn-jn*mn) % un
                    cn = (rn+jn*mn-sn) // un
                    assert (rn+jn*mn) % un == sn
                    for dn in [1, 2, 5]:
                        start_a = max(0, height-jn*dn-cn+int(rn > 0)-int(sn > 0))
                        assert start_a == 0
                        v06_finite["fixed_target_residue_large_j"] += 1
    assert all(carry_boundaries.values()), carry_boundaries

    # Worst permitted resources P=q+1+2t, R=t, K=2t(t-1)/3.
    # The target's extra positive correction is not needed here.
    for qn in range(4, 41):
        for tn in range(3, qn+1):
            kn, rn = Fraction(2*tn*(tn-1), 3), tn
            coefficient = (Fraction(5*tn*tn-17*tn-6, 6)+(tn-1)*(qn-tn))
            assert 6*coefficient == (12*(qn-4)+5*(tn-3)**2+(tn-3)
                                      +6*(tn-3)*(qn-tn))
            assert coefficient >= 0
            for idx in range(1, qn+3):
                ai, ci, bi = C(qn-1, idx-1), C(qn, idx-1), C(qn+1, idx-1)
                gap = (idx*(C(qn+tn+1, idx+1)-C(qn+1, idx+1))
                       -(qn+1+2*tn)*ci-rn*bi-kn*ai)
                assert gap >= coefficient*ci >= 0
                if idx == qn+2:
                    assert ai == ci == 0 and bi == 1
                v06_finite["dense_unified_all_rows"] += 1
        for idx in range(1, qn+3):
            # t=2 keeps the sharper R=0 and integral K<=2 inputs.
            ai, ci, bi = C(qn-1, idx-1), C(qn, idx-1), C(qn+1, idx-1)
            gap = (idx*(C(qn+3, idx+1)-C(qn+1, idx+1))
                   -(qn+5)*ci-2*ai)
            assert gap >= (qn-3)*ci+idx*bi-2*ai >= 0
            v06_finite["dense_t2_retained_rows"] += 1
    # Explicit zero boundary: do not silently strengthen nonnegativity.
    assert (Fraction(5*3*3-17*3-6, 6)+(3-1)*(4-3)) == 0
    assert C(8, 2)-C(5, 2)-11-3-4 == 0  # q=4,t=3,i=1.
    assert C(7, 2)-C(5, 2)-9-2 == 0    # q=4,t=2,i=1.
    finite += sum(v06_finite.values())

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

    if math_only:
        print(json.dumps({
            "status": "PASS_V06_ARITHMETIC_TRANSCRIPTION_CHECKS_ONLY",
            "symbolic_identities": identities,
            "finite_transcription_checks": finite,
            "v05_finite_checks": new_finite,
            "v06_finite_checks": v06_finite,
            "carry_boundaries_exercised": carry_boundaries,
            "partition_sanity_cases": partitions,
            "universal_proof_claimed_by_enumeration": False,
            "files_modified": False,
            "scope": "Polynomial identities and finite transcription/boundary checks; universal proofs are in the manuscript."
        }, ensure_ascii=False, indent=2))
        return

    previous_count = verify_previous_version()
    ancestor_count = verify_ancestor_version()
    dependency_guards = verify_dependency_guards()

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
    chapter_order = ["01_COMMON_JA.md", "02_ORDINARY_JA.md", "03_ENDPOINT_JA.md",
                     "04_WIDTH_JA.md", "04A_ANTIPODAL_JA.md", "05_N4_JA.md",
                     "06_SYNTHESIS_JA.md"]
    assert {chapter.name for chapter in chapters} == set(chapter_order)
    positions = []
    for name in chapter_order:
        chapter = OUT / "chapters" / name
        text = chapter.read_text()
        assert canonical.count(text) == 1, f"Stale/duplicate canonical chapter {chapter.name}"
        positions.append(canonical.index(text))
        for opening, closing in [(r"\(", r"\)"), (r"\[", r"\]")]:
            assert text.count(opening) == text.count(closing), chapter.name
        assert not re.search(r"TODO|TBD|FIXME|PLACEHOLDER", text), chapter.name
    assert positions == sorted(positions), "Canonical chapter order changed"

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
    pdf_checks = verify_pagination()
    previous_comparison = verify_revision_comparison()
    snapshot = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
                for p in sorted(OUT.rglob("*.md"))}
    result = {
        "status": "PASS_PAPER_REDUCTION_TRANSCRIPTION_AND_PRESERVATION_CHECKS",
        "base_commit": BASE,
        "symbolic_identities": identities,
        "finite_transcription_checks": finite,
        "v05_finite_checks": new_finite,
        "v06_finite_checks": v06_finite,
        "carry_boundaries_exercised": carry_boundaries,
        "partition_sanity_cases": partitions,
        "ordinary_checker": "PASS",
        "all_original_tracked_bytes_unchanged": True,
        "previous_v05_files_rehashed": previous_count,
        "previous_v05_file_set_and_bytes_unchanged": True,
        "ancestor_v04_files_rehashed": ancestor_count,
        "ancestor_v04_file_set_and_bytes_unchanged": True,
        "editorial_dependency_guards": dependency_guards,
        "canonical_matches_all_chapters": True,
        "pdf_hash_pages_and_both_output_logs_verified": pdf_checks,
        "previous_revision_comparison_verified": previous_comparison,
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--math-only", action="store_true",
                        help="Check arithmetic without requiring/altering assembled artifacts")
    args = parser.parse_args()
    main(math_only=args.math_only)
