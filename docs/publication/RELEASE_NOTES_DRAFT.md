# NS-P14-Lean — release notes draft

**公開準備用の下書き。リリース・タグ・DOIはまだ発行していない。**

公開時に確定する項目：公開版番号、タグ、対象commit SHA、公開日、
そのcommitに対応する検証記録、配布ファイル名・SHA-256、版DOI。
`lakefile.toml`の`0.1.0`は既存のパッケージ設定であり、公開版の発行記録ではない。

以下の本文は**未完成の開発snapshotを公開すると決めた場合**の候補。
Lean化完成後に公開する場合は、Run20と全域主定理の検証結果を確認して書き直す。

---

NS-P14-Lean is a Lean formalization project concerning total Betti-number
comparisons for tangent cones of numerical semigroup rings and their interval
completions over arbitrary fields.

This development snapshot includes Lean proofs, Japanese manuscripts,
verification scripts, and preserved audit evidence. The whole-P14 formalization
is **not yet complete**. At the preparation baseline, Run19 is recorded as
complete; Run20's global partition and main-theorem composition remain open.
A paper proof, a finite arithmetic check, a previously successful build, and
the kernel verification of a final global theorem are distinct claims.

The pinned environment is Lean `v4.36.0-rc2` with mathlib revision
`139105d28c7685a154cb3093f79edb2e16708099`.
See the README for verification commands and exact evidence scope.
An audit ZIP is not a complete offline checkout and does not contain a
freshly rebuilt mathlib or an installed compiler.

Author: Keisuke Sato ([ORCID](https://orcid.org/0009-0005-4230-0268)).
Original software: Apache-2.0. Original manuscripts and explanatory
documentation: CC-BY-4.0. Third-party terms are preserved; see
[license scope](../../LICENSE_SCOPE.md) and [notices](../../NOTICE).
