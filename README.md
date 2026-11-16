# NS-P14-Lean

Lean formalization of the interval-completion comparison for total Betti numbers
of numerical semigroup tangent cones (NS-P14).

**P14 formalization and final independent audit: complete.**
**全P14のLean形式化・最終独立監査は完了しています。**

Author: **Keisuke Sato** · [ORCID 0009-0005-4230-0268](https://orcid.org/0009-0005-4230-0268)

## Main theorem / 主定理

For every numerical semigroup `S`, every field `k`, and every homological degree
`i`, the total Betti number of the completed tangent cone of `S` is bounded by
that of its literal interval completion. Source and target each use their own
actual minimal atom variables and polynomial ring. No characteristic or
Cohen–Macaulay hypothesis is imposed.

最小importは`NSP14.Main`、公開定理は
[`NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion`](NSP14/Main.lean)です。
引数は`S`・`k`・`[Field k]`・`i`のみです。

```lean
import NSP14.Main

#check NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion
```

## Verified provenance / 検証と監査の根拠

公開版v1.0.0のコード基準は、最終監査後の
`e72713965716d7f93f672034c6332a79b59b1c53`です。
[Run20完了receipt](verification/run20/RUN20_COMPLETE_20261116_R03.json)と
[最終独立監査](verification/run20/independent_audit_20261116_r01/AUDIT_JA.md)・
[監査後push receipt](verification/run20/publication/independent_audit_push_20261116_r01.json)が
全P14の完了、必要な未証明入力なし、未解決指摘なしを記録しています。

- 保存されたcold検証：335 checks、311 fixtures、15,774 declarations、1,019 modules。
- 許容公理：`propext`、`Classical.choice`、`Quot.sound`。
- 正本proof commit：`1a5c6bac9a4fd38a8bc5d13b4c7372e654466e6e`。
- 最終独立cold検証対象：`a5e122a4d09536b1609c5faa8d419f8faf81671f`。

これらは保存済みのLean検証・監査記録です。今回の公開作業では、監査済みファイル・
配布ZIPのハッシュとGit bytesを照合し、公開用文書を整備しています。
**公開用文書の追加を、新たなLean buildや数学的監査の実行とは表示しません。**

## Start here / 読む順序

| 対象 | 入口 |
|---|---|
| 公開主定理 | [Main.lean](NSP14/Main.lean)・[全域分割](NSP14/Main/Partition.lean) |
| 検証結果・再現範囲 | [Run20 README](verification/run20/README.md)・[監査引継ぎ](docs/RUN20_HANDOFF_JA.md) |
| 原稿と実装の対応 | [Run20対応](docs/RUN20_PAPER_CORRESPONDENCE_JA.md)・[50 IDの被覆](docs/RUN20_DEPENDENCY_COVERAGE.json) |
| 日本語の歴史的証明稿 | [V06原稿](proof_sharp_v6/NS_P14_SHARP_PROOF_JA.md)・[V06案内](proof_sharp_v6/README_JA.md) |
| 公開・引用情報 | [v1.0.0説明](docs/publication/RELEASE_NOTES_v1.0.0.md)・[引用情報](CITATION.cff)・[公開記録の案内](docs/publication/README_JA.md) |

V06原稿と下記の過去の進捗節は、その時点の固定SHAを対象とする歴史資料です。
過去の「未完」表示を現在の到達範囲と混同せず、Run20の完了receiptと合わせて読んでください。

## Reproduction / 再現

Pinned Lean: `v4.36.0-rc2`; mathlib:
`139105d28c7685a154cb3093f79edb2e16708099`。
[lean-toolchain](lean-toolchain)・[Lake設定](lakefile.toml)・
[依存lock](lake-manifest.json)を固定しています。
Git・elanと、検証スクリプト用にPython 3.12以降を推奨します。
リポジトリのルートで次を実行します。依存取得にはネットワークと十分なディスク容量が必要です。

```sh
lake update
lake exe cache get
lake build
```

`lake build`はライブラリのビルドです。全受入型・公理依存等を含む保存済みRun20検証を
再現する場合、検証器が旧READMEとfilesetも凍結照合するため、**監査済みcommitの別checkout**を使います。

```sh
git worktree add --detach ../NS-P14-Run20-recheck \
  e72713965716d7f93f672034c6332a79b59b1c53
cd ../NS-P14-Run20-recheck
lake update
lake exe cache get
python3 scripts/verify_run20.py --fresh-project-cache \
  --output-dir verification/run20/runs/local_publication_recheck_01
```

未使用の出力先を選び、古い証跡・ZIPを上書きしないでください。
project lib/IR/tests/auditsはcold再構築し、固定mathlib cacheは保持する検証です。
監査ZIPはコンパイラ・全依存・Git履歴を含む完全offline checkoutではありません。
公開用変更を含むツリー自体のfresh Lean認証とは区別します。

## Citation and licenses / 引用・ライセンス

公開版はv1.0.0です。[CITATION.cff](CITATION.cff)に著者・ORCID・版番号を記載しています。
Zenodo DOIは登録の実測結果を確認してから追記します。

- オリジナルのコード・検証スクリプト：**[Apache-2.0](LICENSE)**
- オリジナルの論文・説明文：**[CC-BY-4.0](LICENSES/CC-BY-4.0.txt)**

[適用範囲](LICENSE_SCOPE.md)と[第三者コードの表示](NOTICE)を参照してください。
引用元の論文・外部依存はそれぞれの権利とライセンスに従います。

## Historical progress / 過去の進捗記録

[Git運用](docs/LEAN_WORKFLOW.md)・[旧監査引継ぎ](AUDIT_HANDOFF.md)・[進捗台帳](LEAN_PROGRESS.md)

## Lean implementation — Run 16

Run16 closes the actual endpoint chain: broad EH normalization, the integer core,
all-competitor kernel and finite stopping, exact endpoint homology/socle,
kernel compensation, general Artin bounds and every full Betti row over any field.
The original narrow completed source has direct entry points
`narrow_endpoint_rows` and `narrow_endpoint_two_rows`.
Final audit/publication state: [Run16 status](docs/RUN16_CLOSURE_STATUS.json).

```sh
python3 scripts/verify_run16.py --fresh-test-cache
```

[Actual exports and review guide](docs/RUN16_AUDIT_HANDOFF_JA.md),
[paper correspondence](docs/RUN16_PAPER_CORRESPONDENCE_JA.md),
[recalibration](docs/RUN16_PLAN_RECALIBRATION_JA.md).
Run15 ordinary closure was completed at `447b7ae`; its original eight goals and
all predecessor evidence are preserved. Kneser/SC, BHP/EK, N4/LTV and the final
P14 synthesis remain Runs17–20. Historical entries below describe their own stage.

## Lean implementation — Run 14

Run14 continuation closes arbitrary-characteristic degree-two Green, one actual
square-zero cut over a fixed same-characteristic infinite extension, sharp offset
volume, the actual truncated P-module tower and minimal-generator quotients,
all bounds for one actual H, and actual NumericalClosure.Data/all_rows with Sidon evidence.
Final machine status is recorded in [closure status](docs/RUN14_CLOSURE_STATUS.json).
This does not yet identify actual Tor bounds or target Betti numbers; those are Run15.

```sh
python3 scripts/verify_run14_continuation.py
```

[Closed exports and Run15 boundary](docs/RUN14_REMAINING_DECLARATIONS_JA.md),
[verification](verification/run14_continuation/verification.json),
[recalibration](docs/RUN14_20RUN_RECALIBRATION_JA.md).
The verifier reruns all predecessor checks and audits every new generated declaration.
The earlier PARTIAL evidence remains frozen in `verification/run14/` and its original ZIP.
Historical verification commands below apply to their original commits; use `d8556dc`
to reproduce Run13 and `8040c90` for the earlier Run14 partial snapshot.

## Lean implementation — Run 13

Actual Koszul/Tor, finite coefficient homology, minimal-resolution ranks, graded Betti,
long exact sequences and rank bounds are connected. Scalar extension preserves total and
graded Betti for actual G/T/A/N/Q with their independently defined order gradings.
The completed-cone and same-jump comparisons use the same actual maps, retaining the shift s.

```sh
python3 scripts/verify_run13_continuation.py
```

[Scope and reproduction](verification/block13_continuation/README_JA.md),
[verification](verification/block13_continuation/verification.json),
[review and fixes](docs/RUN13_CONTINUATION_REVIEW_JA.md),
[Run13 closure and later inputs](docs/RUN13_REMAINING_DECLARATIONS_JA.md).
The full P14 theorem, actual cuts/towers and public inputs remain subsequent work.
The prior partial Run13 evidence stays frozen in `verification/block13/`.

## Lean implementation — Run 12

Actual O_COORD and the formal-series tangent-cone comparison are closed.
The same non-x atom polynomial ring acts on G/T/A/N/Q and surjects onto A/Q.
Opposite homogeneous jump filtrations give an actual S₀-linear same-jump
quotient equivalence with inherited degree shift s. Every terminal has
2≤jump≤ν. The literal k[[S]] tangent cone is naturally graded-k-algebra
isomorphic to the algebraic G, preserving monomials, x, kernels and quotients.

```sh
python3 scripts/verify_block12.py
```

[Scope, exports and tests](verification/block12/README_JA.md),
[verification](verification/block12/verification.json),
[independent implementation review](verification/block12/INDEPENDENT_REVIEW_JA.md).
Twenty runs remain a planning target; stabilization, Koszul/Tor, resource
construction and full P14 are subsequent work.

## Lean implementation — Block 11

The non-Apéry head subspace is now an actual homogeneous ideal N of A.
The actual quotient Q=A/N has the Apéry monomial basis, inherited registered
grading, dimension m, Hilbert counts and top degree ν≤δ+1. The natural map
A_n→Q_n is an isomorphism for n≤2. Actual degree-one atom classes generate Q,
which is Artinian over every field. Completion comparison and jump strata remain separate work.

```sh
python3 scripts/verify_block11.py
```

[Scope and reproduction](verification/block11/README_JA.md),
[verification](verification/block11/verification.json).

## Lean implementation — Block 10

The actual ideal-power quotients now form one commutative k-algebra.
Global monomial coordinates identify the full kernel of multiplication
by x with terminal-supported coordinates, and the actual ring quotient
G/xG with head coordinates. Both bases are proved to be the corresponding
initial monomial classes. Completion comparison and N/Q remain subsequent work.

```sh
python3 scripts/verify_block10.py
```

[Scope and reproduction](verification/block10/README_JA.md),
[verification](verification/block10/verification.json).

## Lean implementation — Block 09

The actual algebraic semigroup ring now has its positive ideal powers
identified with numerical-order coefficient conditions. Exact-order
monomials give finite bases of the homogeneous quotients, with a
well-defined bilinear product and the terminal monomial/kernel criterion.
Completion comparison and the remaining A/T/N/Q module constructions are subsequent work.

```sh
python3 scripts/verify_block09.py
```

[Scope and reproduction](verification/block09/README_JA.md),
[verification](verification/block09/verification.json).

## Lean implementation — Block 08

Actual cofinite additive submonoids now supply multiplicity, unique Apéry
decomposition, finite minimal atom generators, embedding dimension, and
maximum atomic representation length. Apéry degree counts and the
numerical terminal/head bijection are proved across six foundation files.
The identification with the actual completed-semigroup tangent cone and
its modules remains a subsequent step.

```sh
python3 scripts/verify_block08.py
```

[Proof scope, concrete semigroups and reproduction](verification/block08/README_JA.md),
[verification](verification/block08/verification.json).

## Lean implementation — Block 07

Three proof units now form one numerical ordinary comparison:
all-row scalarization, the explicit target margin, and closure for every
cut rank `r >= 2` and every row `1 <= k <= r`.
The target margin uses a short first-difference argument, recorded for the paper.
`NumericalClosure.Data.all_rows` consumes one common finite resource profile
and the small maximal-cut boundary witness.
Actual tower, Tor and Betti constructions remain separate work.

```sh
python3 scripts/verify_block07.py
```

[Scope, inputs and reproduction](verification/block07/README_JA.md),
[verification](verification/block07/verification.json).

## Lean implementation — Block 06

[LargeScalar.lean](NSP14/Ordinary/LargeScalar.lean) extends the large-rank
base to every `r >= 9` and rational `e >= 10`, `d >= a_r`.
It composes with Block03 resources to prove the strict scalar bound.
A continuous floor comparison removes the parity split, and a stronger
first-difference bound permits rational deficit shifts. Both improvements
are recorded in the paper alignment ledger.

```sh
python3 scripts/verify_block06.py
```

[Scope and paper correspondence](verification/block06/README_JA.md),
[verification](verification/block06/verification.json).

## Lean implementation — Block 05

[LargeSeed.lean](NSP14/Ordinary/LargeSeed.lean) proves the harmonic barrier
by induction for every rank `r >= 10`, then proves the base gap
`G_r(10,a_r) > 0` for every `r >= 9`. A direct positive quartic replaces
the paper's convexity-based increment comparison; the paper-ready
replacement is recorded in the alignment ledger.
Extending the base to arbitrary deficit and embedding dimension remains
the next numerical step.

```sh
python3 scripts/verify_block05.py
```

[Scope and paper correspondence](verification/block05/README_JA.md),
[verification](verification/block05/verification.json).

## Lean implementation — Block 04

[LowRank.lean](NSP14/Ordinary/LowRank.lean) proves the finite weighted-row
bounds for all rows at ranks 2 and 3. Rank 2 includes zero deficit and
does not require a triangular lower bound or triangular head cap.
The first row agrees with the existing scalar; rank 3 also receives a
direct adapter from Block03 resources. Actual Koszul/Tor and target
margin constructions remain later tasks.

```sh
python3 scripts/verify_block04.py
```

[Scope, weight table and reproduction](verification/block04/README_JA.md),
[verification](verification/block04/verification.json).

## Lean implementation — Block 03

[Resources.lean](NSP14/Ordinary/Resources.lean) derives SO3 from one finite
resource profile, with arbitrary support and cutoff `n >= r >= 4`.
It composes with Blocks 01–02 to prove the small-rank scalar inequality
from resources and boundary Sidon or numerical Apéry-pair data.
Constructing those inputs from the actual tangent cone remains a later task.

```sh
python3 scripts/verify_block03.py
```

[Scope, paper correspondence and reproduction](verification/block03/README_JA.md),
[verification](verification/block03/verification.json).

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

[Independent Block01 audit](audit/README_JA.md) and
[audit correction and verification](docs/BLOCK01_AUDIT_RESPONSE_JA.md).
The identity permits arbitrary rational shifts; positivity requires natural
shifts, ranks 4–8, and the stated corner condition.


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

## Lean implementation — Run17

Run17 supplies full finite-group Kneser, composite-modulus Savchev–Chen, cyclic growth,
and the same actual-core distance/volume/QC-word consumers. See [Run17 status](docs/RUN17_CLOSURE_STATUS.json),
[exports and audit guide](docs/RUN17_AUDIT_HANDOFF_JA.md), and [paper correspondence](docs/RUN17_PAPER_CORRESPONDENCE_JA.md).
Reproduce with `python3 scripts/verify_run17.py --fresh-test-cache`; each replay uses a new evidence directory.
The selected release evidence is identified by the Run17 status file.
The Run16 section above is its historical snapshot; BHP/EK, N4/LTV and global synthesis remain Runs18–20.
