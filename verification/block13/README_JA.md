# Run13 証明済みexportの監査入口 — 全体未完

基準：Run12 commit `6b8d16889ea9b4d88567f0d9ac70391db2a49824`。
指定指令：`docs/superpowers/plans/2026-11-10-run13-koszul-tor-foundations-order.md`（origin aa133b9）。

**このRun13は指定された完成条件をまだ全て満たしていない。**
`PASS_PROVED_EXPORTS_RUN13_INCOMPLETE` は存在するLean exportと回帰の検査結果であり、X_BASIC/I_FIELD/P14完成の認証ではない。

## 証明済みの入口

| 境界 | 主要export |
|---|---|
| 全e変数のactual最小表示と全次数の斉次性 | `fullPolynomialToG_surjective`, `atomDegreeOneEquiv`, `fullPolynomialToG_linearForm_eq_zero_iff`, `fullPolynomialToG_homogeneous` |
| 実変数Koszul・符号・H₀・上次数消滅 | `koszulList`, `koszul_d_squared`, `koszul_cons_d_first/second`, `koszulH0Equiv`, `koszul_homology_isZero_of_gt` |
| 実有限自由解消 | `polynomial_variable_regular`, `koszul_polynomial_exact_positive`, `koszul_chain_free`, `koszulResolution` |
| 通常Tor | `tensorKoszulIso`, `torKoszulIso`（第二因子の残余体を解消、objectwise） |
| homologyのk有限性 | `koszulVariableHomotopy`, `koszul_homology_action_reduction`, `koszul_homology_finite` |
| totalBettiとactual transport | `totalBetti_iso`, `totalBetti_eq_zero_of_gt`, `totalBetti_free_zero/succ`, `completedTorIso`, `completed_totalBetti`, `jumpStratumTorIso`, `jumpStratum_totalBetti` |
| 実商の標準単項式基底 | `normal_form_exists`, `normal_in_ideal_eq_zero`, `standardMonomialBasis`, `standardMonomialBasis_apply` |
| 任意標数の±1 minor | `signed_unit_determinant_ne_zero`, `signed_integer_minor_rank_lower_bound` |
| 一般短完全複体の局所rank式 | `homology_rank_correction`, `homology_rank_correction_zero` |
| 実flat係数拡大複体のhomology比較 | `fieldExtensionHomologyIso`, `polynomialFieldExtension`, `extendedCoefficientKoszulHomologyIso`, `extendedCoefficientKoszul_finrank` |

上の最後の行は**変更後L[X]加群のKoszul/Betti保存そのものではない**。
一般短完全複体の式も、Koszulが実加群短完全列をそのような複体へ運ぶ未完の接続を含まない。

## 未完と確認点

[正確な未完宣言](../../docs/RUN13_REMAINING_DECLARATIONS_JA.md)を先に読む。
特に通常Tor比較の自然性、極小解消rank/balancing、graded homology/有限台と同jumpの次数差s、
Koszul短完全列・syzygy/有界比較、actual L[X] base change、initial/block rank橋を完成扱いしない。
残余体binomial BettiとP/(X²)の(1,1)数値同定も未完。

Mが有限生成P加群ならchain groupも有限生成P加群である。MがP上自由ならchain groupも自由で、
特にM=Pの解消は有限自由である。一般のchain groupはk上無限次元になり得る。
有限P-homology→全変数annihilation→augmentation factor→有限k-homologyの順序を確認する。
全原子PFと非xのS₀は型で別に保持。S₀→G全射やglobal T≅Nは使わない。
同標数の自然な体拡大だけを扱い、異標数rank一致や全形式級数環tensor同型を仮定しない。

## 再現

```
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block13.py
```

固定Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`。
最終結果・コマンド時間・宣言数は [verification.json](verification.json)。
[declarations.json](declarations.json) は全新規core/fixture宣言（named instanceを含む）。
[DeclarationTypes.lean](DeclarationTypes.lean) と `declaration_types.log` が型・仮定・universe、
`run13_axioms.log` が全新規宣言の公理依存を示す。

既存Block01–11とRun12の全axiom reportを再検査し、旧63 core・旧18 test・固定3依存の84 hashを照合する。
旧検証原本は上書きしない。許容公理はpropext/Classical.choice/Quot.sound。
原稿変更台帳A28–A33、実行台帳、20run再校正を同梱する。

## 受入例の意味

新規testはℕ・二生成元・jump2/3実例、G/T/A/N/Q有限homology、完成/samejump Tor/totalBetti、
標数2・標数2→RatFunc係数拡大、P/(X²)の通常Tor比較/有限性、自由PのBettiと上次数を含む。
1変数Pがk有限生成でないことを別に証明して、chain groupの有限次元性の混入を検査する。
未完の数値例・graded例を合格数へ数えない。

独立read-onlyレビュー：[INDEPENDENT_REVIEW_JA.md](INDEPENDENT_REVIEW_JA.md)。
ZIPとmanifestの詳細は `ARTIFACT_JA.md` を参照する。

## 今回の検証結果

55コマンドが警告なしで成功、970 axiom report（新規229=core183+fixture46、旧741）を検査。
旧84 hashは一致。新規coreは23ファイル・1,852行・88 theorem。
新規の数学公理およびsorry依存は0。検証コマンドの合計実測126.860秒（既存build cacheを使用）。
この時間はrun全体の研究・実装・依存ビルド時間ではない。
