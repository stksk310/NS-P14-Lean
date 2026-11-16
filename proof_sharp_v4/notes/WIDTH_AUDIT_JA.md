# e≥5 幅章の監査・変更記録

読解対象は `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` の `origin/work`。
新稿は `chapters/04_WIDTH_JA.md`。ここでの「形式化済み」は下表の既存exportの型・証明本文を読んだことを意味し、本作業で新しいLean再buildを行ったという意味ではない。

## 採用経路

| 元の節・補題 | 新稿 | 操作 | 数学的な理由 | 対応Lean export（namespace付き） | 新しい形式化 | 状態 |
|---|---|---|---|---|---|---|
| V02§13.1 W1–W3、V03 V.0、各consumer末尾 | 章頭 W-T/W-G/W-F と共通接続章 | 統合 | sourceのcarrier同定、完備接錐、物理幅、target容量、0行/消滅後を共通化 | `NSP14.Endpoint.Data.actual_core_endpoint_bound`; `NSP14.Endpoint.Data.actual_positive_rows_add`; `NSP14.NumericalSemigroup.endpointData_totalBetti`; `NSP14.NumericalSemigroup.interval_completed_betti_lower` | 共通接続lemmaを一つのexportへ束ねるならwrapperのみ | 紙上証明済み・構成要素形式化済み |
| V02§13.2 full AP | W-AP | 保持・適用範囲整理 | narrow仮定 `m≥du+2` では旧 `m=e` 境界は起こらない。`d=1` はtarget容量下界でなく実carrier一致で閉じる | `NSP14.ArithmeticSequence.Data.positiveBettiProfile_upper`; `NSP14.Endpoint.Data.fullAP_carrier`; `NSP14.NumericalSemigroup.narrow_fullAP_comparison` | 不要 | 紙上・Leanとも閉鎖 |
| V02 W5–W12、V03 W_EDGE | W-HOLE | 保持 | one-hole全行には元の整数行列のunit minorと二つの補正単射が必要。単なるHilbert長の粗い上界ではこの狭い境界を払えない | `NSP14.Endpoint.Data.OneHole.actual_boundary_rank`; `.minor_card_pair`; `.actual_upper_add`; `.actual_positive`; `NSP14.Width.edgeCorrection_le_choose`; `.edgeCorrection_le_choose_pred`; `.edgeTopCorrection_le` | 紙上のrank等式自体は不要なら下界だけにできるが、今回本文は監査のため等式を記した。既存Leanは十分な下界を供給 | 紙上証明済み・比較の必要強度は形式化済み |
| V02 W13–W16、V03 W_DENSE | W-DENSE | 統合・保持 | 同じ全Hilbert関数を持つlex商を一つだけ選び、prefix資源→調和補正K→一つの容量差に固定 | `NSP14.Endpoint.Data.dense_resources`; `.exists_core_lex`; `.dense_lex_correction_bound`; `.dense_core_lex_bound`; `.actual_dense_firstterm`; `NSP14.Width.dense_payment`; `NSP14.NumericalSemigroup.narrow_dense_comparison` | 不要。紙上式の並べ替えのみ | 紙上・Leanとも閉鎖 |
| V02 W17–W20、V03 W_SPARSE第一行 | W-S1–4 | 共通化・保持 | 一つの等差和Bと剰余公式を用い、低e四行は係数表一つ、大eは全称二次式一つ | `NSP14.Endpoint.Data.wordVolume_le_growthVolume`; `.wordVolume_quadratic_bound`; `.actual_first_volume_third`; `.actual_first_volume_fourth`; `.actual_first_sparse_six`; `.actual_first_sparse_seven`; `.actual_first_sparse_eight`; `.actual_first_sparse_nine`; `.actual_first_sparse_large` | 不要 | 紙上・Leanとも閉鎖 |
| V02§13.4第二行 e=7 と e≥8 | W-S7 | 統合（議論そのものの枝削減） | `e=7+v,u=2e−2+z` の一つの非負多項式 `2v²+5vz+12v+2z²+21z+4` が全e≥7を払う | `NSP14.Width.sparse_second_payment` | 不要。既存Leanが既にこの統一を実装 | 紙上・Leanとも閉鎖 |
| V02 W21、V03 V.3末尾 | W-S8 | 保持 | 第二行からtopまでの正規化容量単調性を一度だけ示す。`e−i` で割らない | `NSP14.Width.normalized_capacity_base`; `.normalized_capacity_step`; `.chooseRatio_adj`; `.normalized_capacity_monotone`; `NSP14.Endpoint.Data.actual_sparse_resource_add`; `.actual_sparse_higher` | 不要 | 紙上・Leanとも閉鎖 |
| V02 W22、V03 V.4の b1≤P+2・b3≤P−1・Euler による b2≤2P | W-G/W-5G | 削除・置換（数学的仕事を一つ削減） | 専用三変数Euler評価を使わず一般rank envelopeをそのまま使用。u6/7の第2行は40/62から44/68に緩まるがtarget46/77が払う | `NSP14.Endpoint.Data.actual_positive_rows_add`; `.actual_five_small_positive` | 不要 | 紙上・Leanとも閉鎖 |
| V02§13.5 u6/7第一行 | W-FIVE-SMALL | 保持・条件明示 | 元のR>0のときだけHx≥3、真の高次QC基底が生じてb1≤9へ改善。反射やRhat>0へのすり替えを行わない | `NSP14.Endpoint.Data.coreHilbert_two_add_five_le_P_of_R_pos`; `.QCore_five_seven_first`; `.actual_five_small_first` | 不要。本文はdegree≥4というcore座標の説明も残すが、既存Leanに必要なのはdegree≥3 | 紙上・Leanとも閉鎖 |
| V02§13.5高次行の専用sharp bound | W-FIVE-HIGH | 置換・共通化 | 一般envelopeで全構造を統一。ただしu8にW≤14を保持し、u≥9に正三次多項式を一つ置く | `NSP14.Width.five_wordVolume_eight`; `NSP14.Endpoint.Data.actual_five_higher`; `NSP14.Width.choose_quadratic_step`; `.choose_quadratic_from_eight` | 不要 | 紙上・Leanとも閉鎖 |
| V02 W23–W24 | W-FIVE-FIRSTの非antipodal部分 | 保持・算術の配置整理 | Kneserの唯一の小増分を二coset構造に同定し、それ以外は増分3。exact等差和を使う短い紙上routeを残す | `NSP14.Additive.twoCoset_antipodal`; `.fourPoint_growth`; `NSP14.Endpoint.Data.five_nonAntipodal_volume`; `.actual_five_nonAntipodal_first` | 各u mod3の三式をnamed exportにする作業だけ未実施。現在のLeanは同じ比較を粗い剰余上界＋u8–11で証明 | 紙上証明済み・比較はLean済み／紙の算術経路完全一致は未形式化 |
| V02 W25 exact presentation/P/W/b1 | 04A APD.1–2 | 削除・置換 | 候補語spanningからPの上界だけを得て第一行調和評価。高次はW-FIVE-HIGHを共有する | `NSP14.Endpoint.Data.antipodal_coreP_bound`; `NSP14.Endpoint.Data.actual_antipodal_first` | 04Aの対応台帳を参照 | 04Aの証明・監査に従う |
| V03 W_CLOSE | §4.5 | 保持・共通接続へ統合 | e≥6の二端幅/密幅/疎幅、およびe5のu4/5/6/7/≥8は重なりなしで隙間なく覆う | `NSP14.NumericalSemigroup.narrow_width_comparison` | 不要 | 紙上・Leanとも閉鎖 |

上記には「付録へ移しただけ」のものはない。exact antipodal成果は既存ファイルに保存したまま主定理の経路から外し、本稿に必要な付録として再掲することも要求しない。
他方、generic rank envelopeへの統一はu8で一つの資源チェックを増やすため、その箇所だけを見て純粋な行数減と数えない。効用は専用sharp boundへの依存を削ることである。

## 保持した監査点

- `P_C` と `P_G` を区別し、QC→QG実核の長さによるTor補償は端点章に残す。
- 元のRと元のHxを固定。one-hole反射はcore基底を数えるためだけに用い、Rを反射しない。
- one-holeの行ごとのcolumn選択は元の整数微分に対角±1 minorを作る。標数2でも単位が消えない。
- lexは各行別々でなく一つの全Hilbert関数に対して選ぶ。親子の分数重みは整数計数であり体内の除法ではない。
- `m=du+2` を除外せず、uとduを別記。full APのd1は実半群一致を使う。
- 正規化容量のtop行は正の `C(e,e)=1` で割るだけで、`e−i` では割らない。
- 差式は有理数/整数上で記す。LeanのNat減算は `actual_positive_rows_add` の加法形からのみ回収する。
- u8の五生成元第二行はquadratic resourceだけでは閉じない。`W≤14` を落とさない。
- 196組、83組・665比較・5tailのいずれも本章の依存には戻していない。

## 非採用の短縮案

one-holeを一般Artin長だけで処理する案、denseとsparseを一つのquadratic resourceだけで処理する案、五生成元u8の第二行でexact有限和を捨てる案は採用しない。いずれも狭い境界でtarget容量の余裕を失い、現時点で短い全称代替証明を供給できないためである。
本章には未証明の新統一補題を採用していない。

## 今回実施した検算

SymPy 1.14.0 で次の9本の恒等式を記号的に展開し、差がすべて0であることを確認した：
等差和のquadratic差、e≥7の第二行多項式、五生成元u≥9の第二行三次差、dense大tの非負係数表示、sparse第一行e6–9の四つの表式、およびe≥10の第一行差。
さらにPythonの整数・有理数演算で、one-holeの二補正上界（q3–29）、dense支払い（q4–34）、sparse全高次行（e6–34）、五生成元非antipodal第一行・高次行（u8–500）の計50,907件を検算して全件成功した。
これらは転記・算術整合性の補助検査であり、全称証明を有限検算で代替していない。
本章の全称性は、本文に展開した単射、非負係数恒等式、Kneser、元の単位minor、容量単調性による。
今回この担当ではLean/lakeのfresh buildは実行していない。
