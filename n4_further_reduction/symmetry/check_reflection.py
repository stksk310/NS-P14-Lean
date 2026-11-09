#!/usr/bin/env python3
"""Independent core-reflection certificate; does not alter the V02 certificate.

Compute one standard-word set per reflection orbit, both endpoint heights,
and an envelope valid for each of the two original orientations.  Compare
the reconstructed oriented rows with the frozen V02 data as an audit only.
The all-m,d justification is in ../SYMMETRY_SEARCH.md, not a sample of m,d.
"""

from argparse import ArgumentParser
from collections import deque
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import hashlib
import json


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "proof_integrated_v2/certificates/n4/SHORTER_N4_CERTIFICATE.json"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def reflection(u, a, b):
    return u - b, u - a


def core(u, a, b):
    """Use homogeneous fibers, independently of the V02 implementation."""
    layer = {0}
    standard = {(0, 0)}
    for n in range(1, u):
        for s in range(n + 1):
            t = n - s
            offset = a * s + b * t
            if offset not in layer and offset - u not in layer:
                require(n <= u - 2, "N13 cutoff")
                standard.add((s, t))
        layer = {offset + step for offset in layer for step in (0, a, b, u)}

    require(all((s == 0 or (s - 1, t) in standard)
                and (t == 0 or (s, t - 1) in standard)
                for s, t in standard), "divisor closure")
    sigma = sum((s + 1, t) not in standard and (s, t + 1) not in standard
                for s, t in standard)
    Hx = max(s + t - (a * s + b * t + u - 1) // u
             for s, t in standard)
    Hv = max((a * s + b * t) // u for s, t in standard)

    distance = [None] * u
    distance[0] = 0
    todo = deque([0])
    while todo:
        r = todo.popleft()
        for step in (a, b):
            dest = (r + step) % u
            if distance[dest] is None:
                distance[dest] = distance[r] + 1
                todo.append(dest)
    require(None not in distance, "primitive directed reachability")
    W = 1 + sum(distance)
    h = u // 2
    require(sigma <= h + 1, "stronger mixed-corner socle bound")
    require(all(s + t <= h for s, t in standard if s and t), "mixed cutoff")
    return dict(P_C=len(standard), sigma_C=sigma, Hx=Hx, Hv=Hv, W=W)


def oriented_row(u, a, b, data, reflected=False):
    Hx = data["Hv" if reflected else "Hx"]
    Rhat = min(data["W"] - u, u * max(Hx - 2, 0))
    upper = data["P_C"] + data["sigma_C"] + 1 + Rhat
    lower = comb(u, 2) + 1
    return dict(a=a, b=b, w=u, P_C=data["P_C"],
                sigma_C=data["sigma_C"], Hx=Hx, W=data["W"],
                Rhat=Rhat, U1=upper, F1_min=lower, slack=lower - upper)


def unit_counterexample(rows):
    """Return the first actual failure of unit invariance of P_C/sigma_C."""
    for (u, a, b), data in sorted(rows.items()):
        for unit in range(2, u):
            if gcd(unit, u) != 1:
                continue
            c, d = sorted((unit * a % u, unit * b % u))
            other = rows[u, c, d]
            if (data["P_C"], data["sigma_C"]) != (
                    other["P_C"], other["sigma_C"]):
                return dict(u=u, offsets=[a, b], unit=unit, image=[c, d],
                            original={k: data[k] for k in ("P_C", "sigma_C", "W")},
                            transformed={k: other[k] for k in ("P_C", "sigma_C", "W")})
    raise AssertionError("Expected a counterexample to unit invariance")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("REFLECTION_CERTIFICATE.json"))
    parser.add_argument("--source", type=Path, default=SOURCE)
    args = parser.parse_args()

    source_bytes = args.source.read_bytes()
    source = json.loads(source_bytes)
    source_rows = {(r["w"], r["a"], r["b"]): r for r in source["rows"]}
    oriented, orbits, by_width = {}, [], []
    for u in range(3, 13):
        local = []
        for a, b in combinations(range(1, u), 2):
            if gcd(gcd(a, b), u) != 1:
                continue
            c, d = reflection(u, a, b)
            if (a, b) > (c, d):
                continue
            require(reflection(u, c, d) == (a, b), "reflection involution")
            data = core(u, a, b)
            original = oriented_row(u, a, b, data)
            reverse = oriented_row(u, c, d, data, reflected=True)
            members = [[a, b]] if (a, b) == (c, d) else [[a, b], [c, d]]
            envelope_R = min(data["W"] - u,
                             u * max(max(data["Hx"], data["Hv"]) - 2, 0))
            envelope = data["P_C"] + data["sigma_C"] + 1 + envelope_R
            require(envelope == max(original["U1"], reverse["U1"]),
                    "symmetric envelope equals the worse oriented bound")
            if len(members) == 1:
                require(data["Hx"] == data["Hv"], "fixed-point endpoint heights")
                require(original == reverse, "fixed-point reconstruction")
            oriented[u, a, b] = original
            oriented[u, c, d] = reverse
            record = dict(u=u, representative=[a, b], members=members,
                          orbit_size=len(members), **data,
                          Rhat_envelope=envelope_R, U1_envelope=envelope,
                          L1=comb(u, 2) + 1,
                          envelope_slack=comb(u, 2) + 1 - envelope,
                          oriented_slacks=[original["slack"]] if len(members) == 1
                                          else [original["slack"], reverse["slack"]])
            orbits.append(record)
            local.append(record)
        fixed = sum(r["orbit_size"] == 1 for r in local)
        by_width.append(dict(u=u, oriented_count=sum(r["orbit_size"] for r in local),
                             fixed_count=fixed, orbit_count=len(local),
                             min_envelope_slack=min(r["envelope_slack"] for r in local)))

    require(oriented == source_rows, "all reconstructed oriented V02 rows agree")
    require(len(oriented) == 196, "oriented count")
    require(len(orbits) == 109, "reflection orbit count")
    require(sum(r["orbit_size"] == 1 for r in orbits) == 22, "fixed count")
    failures = [[r["u"], *r["representative"]]
                for r in orbits if r["envelope_slack"] < 0]
    require(failures == [[3, 1, 2], [4, 1, 3]], "exact envelope failures")

    refined = [r for r in orbits if r["u"] != 11]
    manual_small = [r for r in refined if r["u"] <= 4]
    nontrivial = [r for r in refined if r["u"] >= 5]
    require(len(refined) == 84, "refined-tail orbit count")
    require(sum(r["orbit_size"] for r in refined) == 151, "refined-tail pair count")
    require(len(manual_small) == 3 and len(nontrivial) == 81, "paper-small-width split")
    require(all(r["envelope_slack"] >= 0 for r in nontrivial),
            "all 81 remaining representatives pass")

    result = dict(schema="N4_CORE_REFLECTION_SEARCH_V1",
                  source=str(args.source.relative_to(ROOT))
                         if args.source.is_relative_to(ROOT) else str(args.source),
                  source_sha256=hashlib.sha256(source_bytes).hexdigest(),
                  core_computations=len(orbits), reconstructed_oriented_rows=len(oriented),
                  fixed_count=22, reflection_orbits=109, envelope_failures=failures,
                  refined_tail=dict(omitted_width=11, oriented_count=151,
                                    reflection_orbits=84, explicit_small_core_types=3,
                                    remaining_finite_representatives=81,
                                    min_remaining_envelope_slack=min(
                                        r["envelope_slack"] for r in nontrivial)),
                  unit_invariance_counterexample=unit_counterexample(oriented),
                  multiplicities_enumerated=0, by_width=by_width, orbits=orbits,
                  qualification="Core symmetry and symmetric all-orientations envelope; "
                                "no assertion that actual tangent-cone Betti numbers or "
                                "actual R are reflection invariant.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "orbits"},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
