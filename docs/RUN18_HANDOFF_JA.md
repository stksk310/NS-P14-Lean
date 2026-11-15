# Run18 引継ぎ：公開証明と型

数学的な六IDは `audit/run18/ClosedGoals.lean` の `NSP14.Run18.all_closed` に集約した。最終cold検証・独立レビュー・COMPLETE ZIP・通常Pushの認証状態は [CLOSURE_STATUS](RUN18_CLOSURE_STATUS.json) と [最終レビュー](RUN18_FINAL_REVIEW_JA.md) が記録する。

| 利用目的 | 実export |
|---|---|
| 任意標数・一般斉次商の全graded BHP | `NSP14.Lex.quotientGradedBetti_le_lex` |
| 同じ商のpositive total行比較 | `NSP14.Lex.quotientTotalBetti_le_lex` |
| 元の体上の一つのwhole-Hilbert lex ideal | `NSP14.Lex.exists_lex_sameHilbert` |
| actual lex / strongly stable graded EK | `IsLex.graded_ek` / `IsStronglyStable.graded_ek` |
| 実QCの一つのlex model | `Endpoint.Data.exists_core_lex` |
| 原稿のS_j・実g_j・同じK | `standardPrefixCard`、`max_generator_recurrence`、`lexCorrection_eq_prefix_sum` |
| 元の実full Gのdense第一項上界 | `Endpoint.Data.actual_dense_firstterm` |
| 元のSのdense第一項・literal comparison | `narrow_dense_firstterm` / `narrow_dense_comparison` |
| 全物理狭幅・五生成元以上・全行 | `NumericalSemigroup.narrow_width_comparison` |
| 六つの元の凍結型 | `NSP14.Run18.all_closed` |

全域定理の入口は元の `S : NumericalSemigroup`、任意 `k : Type` と `[Field k]`、`5≤S.embeddingDimension`、`S.width≤S.multiplicity−2`、任意 `i : ℕ`。結論は元の `S.FormalTangentAlgebra k` のactual最小変数でのtotalBettiと、literalな `S.intervalCompletion` のactual最小変数でのtotalBettiの比較である。正規化はV=d*uを保ち、実kernel補償と元のRを経由する。

Run18の数学的な未完型は残っていない。従来のBHP/EK・lex存在・dense/globalの未完記述は過去checkpointの履歴として残した。新しい証明に未証明のTor比較、resolution、Cohen–Macaulay性、P_C=P_G、d=1の前提は加えていない。

原稿のg_j差分は加法形で扱う。任意のprefix変数数q≥1について、actual最大変数qの最小生成元数とactual Hilbert/standard prefix countの再帰を証明し、actual weighted generator identityから有限和をtelescopeする。高次Kの重み評価はactual suffix商へのfirst harmonic boundで供給する。

旧verification/artifactのbytes、固定RequestedGoals、固定指令書を保持する。生成された最新ZIPの全entry/hash/CRCとproof/evidence/review Git bindingは公開用packagerで検査する。Run19の計画・開始は別のユーザー指示に従う。
