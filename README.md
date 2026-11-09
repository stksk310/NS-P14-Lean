# NS-P14-Lean

Lean開発・監査ブランチ：`work`。今後の関連成果物のPushはユーザー承認済み。
[Git運用と承認記録](docs/LEAN_WORKFLOW.md)／[監査引継ぎ](AUDIT_HANDOFF.md)

## Lean implementation — Block 02

[Sidon.lean](NSP14/Combinatorics/Sidon.lean) proves the finite-group difference
injection, cyclic cardinality bound, and a numerical Apéry-pair witness bridge.
It connects boundary Sidon witnesses to Block01 without a separate bad-corner
hypothesis. Construction of those witnesses from the actual maximal Q2 remains
an explicit later task; no tangent-cone or Betti completion is claimed here.

```sh
python3 scripts/verify_block02.py
```

[Exact scope and reproduction](verification/block02/README_JA.md) and
[compiled verification](verification/block02/verification.json).


## Lean implementation — Block 01

The first compiled block is [SmallScalar.lean](NSP14/Ordinary/SmallScalar.lean):
the five exact small-rank scalar rows, the universal shifted-gap identity and
positivity for all natural shifts with an explicit corner-exclusion premise.
This is the numerical part of V03 O_SMALL, not a proof of actual cone/Betti
semantics or of the Apéry–Sidon feasibility premise.

Pinned Lean: `v4.36.0-rc2`; mathlib: `139105d28c7685a154cb3093f79edb2e16708099`.

```sh
python3 scripts/verify_block01.py
```

With standard elan, `lean-toolchain` selects the compiler. In this cloud session,
the official GitHub compiler was installed at `/tmp/ns-p14-lean`:

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block01.py
```

For a fresh checkout with cache access blocked, use
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`, then build from source.
[Scope and reproduction](verification/block01/README_JA.md),
[compiled verification](verification/block01/verification.json), and
[progress](LEAN_PROGRESS.md).


Lean formalization project for NS-P14.

## Mathematical source

Latest integrated manuscript V02 (2026-11-09):
[single Japanese proof](proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md),
[replacement ledger](proof_integrated_v2/PROOF_REPLACEMENT_LEDGER.md),
[coverage](proof_integrated_v2/GLOBAL_COVERAGE_MATRIX.md), and
[reproduction guide](proof_integrated_v2/README_REPRODUCE.md).

V02 integrates the audited simplifications, centralizes the endpoint
kernel–Tor argument, replaces N4 higher-row campaigns by universal bounds,
and reduces its first-row certificate from 13,921 to 196 offset pairs.
The original complete manuscript and all earlier certificates are preserved
in [proof_complete](proof_complete/README_JA.md).

This is a human, computer-assisted proof candidate with named published
inputs and exact finite integer lemmas. It is not Lean kernel verification.

Previous conditional reduction:
[report](proof_reduction/FINAL_REPORT_JA.md),
[proof](proof_reduction/HUMAN_PROOF_REDUCED.md), and
[historical dependency ledger](proof_reduction/DEPENDENCY_AND_GAP_LEDGER.md).

Earlier consolidation:

- [単一証明の作業稿](proof/NS_P14_SINGLE_PROOF_JA.md)
- [検証境界と残る依存](proof/AUDIT_JA.md)
- [厳密算術の検証記録](proof/verification.json)

The earlier main argument is consolidated around one Apéry tower and one cut. The
ordinary-target argument now reaches embedding dimension `e >= 13`, using
200 exact rational coefficient checks and an analytic tail. Small embedding
dimension and narrow targets retain explicit inherited boundary theorems.

The earlier consolidation and conditional reduction remain unchanged as
historical records. The current mathematical status is recorded in
the complete manuscript above.

```sh
python -B proof/checks/verify_scalar.py
python -B proof/checks/recheck_rows.py
```
