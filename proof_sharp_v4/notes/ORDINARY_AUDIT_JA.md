# ordinary 章：採用・対応・検証記録

対象 commit：345e2d82fea50ef89e00a8f35c4fb53ac601d7ce。
2026年11月15日（JST）。旧稿・本番 Lean・凍結命題・旧証跡は変更していない。
本文は chapters/02_ORDINARY_JA.md。以下の O1–O12 はその補題番号である。

## 採用した数学的削減

| 元の節・補題 | 新しい節・補題 | 操作 | 数学的理由 | 正確な Lean export | 新しい形式化 | 状態 |
|---|---|---|---|---|---|---|
| V02 §8 (8.3) の完全余剰式と評価 | §2.5 O6、(O12) | 置換・議論そのものを削減 | 必要なのは下界だけ。R の δ 一階差分を足せば全行容量が直接出る | NSP14.Ordinary.TargetMargin.target_zero / target_step / capacity_step / target_margin | 不要 | 紙上証明・既存 Lean 形式化済み |
| V02 §11 (S14)、(S17)–(S19) | §2.9 (OL3)–(OL4) | 置換・議論そのものを削減 | 調和増分を最初の項で抑え、障壁増分と正係数 quartic で直接比較。凸性・中間 2/r の補題は結論に不要 | NSP14.Ordinary.LargeSeed.harmonic_cutoff_step / barrier_step_identity / harmonic_lt_barrier | 不要 | 紙上証明・既存 Lean 形式化済み |
| V02 §11 (S24)–(S25) の F₀/F₁ 比較 | §2.9 (OL8) | 置換・議論そのものを削減 | 床の下限 2D≥a+1 と一つの有理恒等式で連続比較。偶奇を区別しない | NSP14.Ordinary.LargeScalar.floor_comparison_identity / floorStep_gt / baseStep_gt | 不要 | 紙上証明・既存 Lean 形式化済み |
| SO4 と V02 (S30) の同型の差分計算 | §2.7 O8、(O17) | 統合 | 任意の基点 e₀ について一つの二次多項式恒等式を証明し、小 rank は e₀=r+1、大 rank は e₀=10 を代入 | NSP14.Ordinary.SmallScalar.gap_shift、および NSP14.Ordinary.LargeScalar.quadrant_identity が両実使用形を形式化 | 任意 e₀ 版を独立 export にするなら ring 型の一般化補題を追加。主定理の二つの代入形には不要 | 任意 e₀ の本文 statement は紙上証明済み・その一般形の単独 Lean export は未追加。実使用形は形式化済み |
| V02 §11 の r=4,…,8 seed 行・tail Cauchy 比較 | §2.8 O10 と §2.9 r=9 の一つの seed | 削除（V03 既採用の方針を完全本文へ反映） | 小 rank は SO4 五行表で全域閉鎖。大 rank 入口は r≥9 なので古い五 seed に用途がない | NSP14.Ordinary.SmallScalar.small_gap_pos / NSP14.Ordinary.LargeSeed.rank_nine_seed / large_seed_pos | 不要 | 紙上証明・既存 Lean 形式化済み |
| V02 §9 の r=3 余裕の整数二項係数展開 | §2.6 O7 | 置換 | z=δ−6,s=e−4 で非負係数多項式を一度表示 | NSP14.Ordinary.LowRank.rank_three_margin_pos | 不要 | 紙上証明・既存 Lean 形式化済み |
| V02 §15、first-hit、truncated lex、83 profile・665比較・5tail | 全 ordinary 経路 | 主依存から削除（V03 既採用を維持） | O9–O10 が e=5,…,9 の残りを全称恒等式で閉じる | NSP14.Ordinary.NumericalClosure.Data.all_rows / NSP14.Ordinary.ordinary_betti_bound | 不要 | 新発見ではなく、現行の安全な依存削減を保持 |

上の削減は付録移動で短く見せたものではない。旧証明は歴史的資料として残るが、
この章の数学的依存はそれらを使わない。反対に、以下の説明は監査に必要なので短さのために削らなかった。

## 保持した核心と既存 export

以下で NumericalSemigroup 以下の namespace は NSP14.NumericalSemigroup、
LinearCutData はその namespace 内である。

| 本文 | 保持した数学的仕事 | 対応する既存 export（代表） |
|---|---|---|
| O1 | actual 数値座標、非 Apéry イデアル、逆向き filtration の同 jump stratum。T と N 全体は同型視しない | NumericalSemigroup.jump_stratum_coordinate_action / jumpStratumEquiv / towerStratumEquiv / LinearCutData.towerStratumCutIso |
| O2 | 最小 offset prefix、原子剰余と非原子剰余の区別、有限停止、総量 | NumericalSemigroup.order_stabilization / offsetLevel_path_bound / offset_volume_bound / terminal_finite |
| O3 | 一つの cut、actual 完全列、一つの資源列の区間計数 | NumericalSemigroup.LinearCutData.cutTower_exact / cutTower_generated / sameJumpCutIso_degree、NumericalSemigroup.towerResource_zero / actualNumericalData / actual_all_rows |
| O4 | 初項加群への rank 比較と、各多重次数の対角 ±1 minor。有理平均は数値 rank の評価 | NSP14.Homological.generated_harmonic_bound / harmonic_bound / standard_harmonic_bound |
| O5 | 実際の d₂、同 jump filtration、短完全列を通る三段鎖。connecting rank の補数も非負の減算 | NSP14.NumericalSemigroup.LinearCutData.cutTower_combined / cutTower_resource_row、NSP14.Ordinary.ActualWitness.actualTor_resource_row / actualTor_target_row |
| O6 | 第0 homology の定数 q 補正、actual target 差の厳密係数、j>r の余り | NSP14.Ordinary.ActualWitness.nativeFull_corrected_bound / correctedFullTransfer / actualTor_target_row_all |
| O7 | r=2 の δ=0、r=3 の二つの同時 head 上界、top を含む全 rank scalar 化 | NSP14.Ordinary.LowRank.Layers.rank_two_bounds / rank_three_bounds、NSP14.Ordinary.Scalarization.row_le_scalar |
| O9 | maximal q₂ から actual Apéry 残余の強い Sidon 性、反復項・異次数の衝突排除 | NumericalSemigroup.maximal_qDegree_multiplicity_bound / maximal_qDegree_deficit_bound |
| O10 | 五行表は整数シフト s,t≥0、負 seed は actual 性で排除 | NSP14.Ordinary.SmallScalar.row4 / row5 / row6 / row7 / row8 / small_gap_pos |
| O11 | 大 rank seed と正係数障壁、floor 比較、二方向への正値延長 | NSP14.Ordinary.LargeSeed.large_seed_pos、NSP14.Ordinary.LargeScalar.large_gap_pos、NSP14.Ordinary.SmallScalar.Resources.scalar_lt_large |
| O12 | 元の任意体の completed source、literal interval target、各自の最小変数、全行 | NSP14.Ordinary.ordinary_actual_completion_betti_le |

O1–O12 の採用経路に未証明の数学的候補は混ぜていない。
一般基点 e₀ の O17 だけは紙上で新たに一つへまとめた statement である。
元の二つの特殊化に既存 Lean があることと、一般 statement の新 export が存在することは区別する。

## 公刊入力の範囲

- Green：無限体の標準次数付き代数の次数 2 の超平面制限上界。Caviglia の
  A hyperplane restriction theorem and applications to reductions of ideals, §1 (1.1) に再掲された任意標数版。
  必要な有限体では同標数の純超越拡大を先に行い、Betti 数を flat base change で戻す。
- 算術列 target：Gimenez–Sengupta–Srinivasan, arXiv:1108.3203, Theorem 4.1 と
  Herzog–Stamate, arXiv:1308.4644v3, Proposition 2.5 の任意体の範囲。
  ordinary completion は m,…,2m−1 なので βᵢ=i choose(m,i+1) を適用する。
- Koszul、長完全列、bounded 二重複体、Hilbert syzygy、自由解消の rank Euler、初項加群の
  Gröbner normal form は通常の基礎代数。スペクトル系列の退化や商の Betti 単調性を外部入力に含めない。

## 読んだ資料と検証の範囲

依頼全文、V03 ordinary Part と O_* registry、V02 §2–11、
CORE_READABILITY_AUDIT.md、ORDINARY_PAPER_REDUCTION_JA.md、
SIDON_INDEPENDENT_AUDIT.md、LEAN_PAPER_ALIGNMENT_JA.md A01–A09 と actual 接続の記録、
上表の Lean ファイル・実際の export 型を照合した。
独立担当は大 rank の記号恒等式と §2.1–2.8 の接続を別に再読し、
数学的欠落は報告しなかった。inline 数式開始記号の転記ミスは修正した。

実行した補助検算：

1. python3 -B auditability_search/ordinary/verify_ordinary_reduction.py
   は FIVE_EXACT_SCALAR_ANCHORS_PAID と終了し、五行の正確な係数を確認した。
2. python3 -B proof_sharp_v4/checks/check_ordinary_identities.py
   は SymPy で一般基点を含む 11 恒等式、Fraction で五行と二つの大 rank 初期値を確認する。
   このスクリプトは資料の転記と式変形の検算であり、全称性は本文の帰納法・符号分解・単射で証明している。
3. inline の開始・終了区切りの個数、表示数式区切り、残留 placeholder を点検する。

この担当では Lean を再実行していない。上表の「形式化済み」は固定 commit 内に該当する
証明・型が存在することを読んだ記録であり、この新稿全体の新たな kernel 認証という意味ではない。
公刊定理原典の全面再査読も実施していない。

## coverage と頁数に関する引渡し

ordinary で e≥3 の全 source は 2≤r≤e−1 に入り、r=2,3 / 4,…,8 / r≥9 の三枝で尽きる。
相対 j=r、δ=0、i=0、i=e、i>e は本文で処理している。
e=1,2 および narrow source はこの章の仮定外であり全体合成の別枝へ渡す。

章単独の実測頁数は未測定。V03 の328行の骨子との行数比較を「証明の膨張」とは扱わない。
本章は V02 の必要完全証明と CORE の欠落接続を本文へ展開したものだからである。
比較対象は同じ監査水準の一本化原稿であり、A05/A06/A08 の三経路の削減と
O17 の差分統合を実削減として数える。全体の11pt組版を親担当で測定する。
