#!/usr/bin/env python3
"""Read the 200 rows through the alternative gap identity, without imports
from the producer. This checks arithmetic, not the mathematical reductions.
"""
from fractions import Fraction
from pathlib import Path
import json


def main():
    root = Path(__file__).resolve().parents[1]
    certificate = json.loads((root / "certificates/scalar_e13.json").read_text())
    rows = certificate["all_exact_rows"]
    if [row["delta"] for row in rows] != list(range(10, 210)):
        raise ValueError("missing or duplicate defect")
    for row in rows:
        d = row["delta"]
        p = 0
        while (p + 1) * (p + 2) // 2 <= d:
            p += 1
        if p != row["r"] or row["initial_e"] != 13:
            raise ValueError((d, "wrong envelope or initial e"))
        harmonic = sum((Fraction(1, n) for n in range(1, d + 1)), Fraction())
        alpha = Fraction(p - 1, d + 1)
        half = Fraction(d + p - 2, 2)
        h = half - (p - 1) * harmonic
        bonus = (Fraction(p + 1, 2) - alpha) * (p * (p + 1) // 2)
        gap13 = 12 * (half - alpha) + (d + 12) * h + bonus
        gap14 = 13 * (half - alpha) + (d + 13) * h + bonus
        slope = gap14 - gap13
        if (gap13 != Fraction(row["gap"]) or slope != Fraction(row["slope"])
                or gap13 <= 0 or slope <= 0):
            raise ValueError((d, "gap or slope mismatch"))
    h210 = sum((Fraction(1, n) for n in range(1, 211)), Fraction())
    if h210 >= 6 or str(h210) != certificate["H210"]:
        raise ValueError("analytic base mismatch")
    index = json.loads((root / "SOURCE_INDEX.json").read_text())
    import hashlib
    for record in index["files"]:
        if hashlib.sha256((root / record["file"]).read_bytes()).hexdigest() != record["sha256"]:
            raise ValueError((record["file"], "literal source mismatch"))
    print(json.dumps({"status": "PASS_SECOND_DERIVATION_AND_SOURCE_BYTES",
                      "exact_rays": len(rows), "H210_lt_6": True,
                      "literal_source_files": len(index["files"]),
                      "scope": "A second calculation of finite coefficients and "
                               "source hashes; not independent mathematical "
                               "or Lean verification."}, indent=2))


if __name__ == "__main__":
    main()
