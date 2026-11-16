# V06：e≥5 幅章の監査・変更記録

読解対象は `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` の `origin/work`。
新稿は `proof_sharp_v6/chapters/04_WIDTH_JA.md`。V04とV05の原稿・監査記録は各旧ディレクトリに保存する。
下表はV06で採用する経路を記す。ここでの「既存形式化済み」は下表のexportの型・証明本文を読んだことを意味し、本作業で新しいLean再buildを行ったという意味ではない。
V05・V06で追加した紙上経路と、同じ結論を与える既存Leanの別経路は区別する。

## 採用経路

| 元の節・補題 | 新稿 | 操作 | 数学的な理由 | 対応Lean export（namespace付き） | 新しい形式化 | 状態 |
|---|---|---|---|---|---|---|
| V02§13.1 W1–W3、V03 V.0、各consumer末尾 | 章頭 W-T/W-G/W-F と共通接続章 | 統合 | sourceのcarrier同定、完備接錐、物理幅、target容量、0行/消滅後を共通化 | `NSP14.Endpoint.Data.actual_core_endpoint_bound`; `NSP14.Endpoint.Data.actual_positive_rows_add`; `NSP14.NumericalSemigroup.endpointData_totalBetti`; `NSP14.NumericalSemigroup.interval_completed_betti_lower` | 共通接続lemmaを一つのexportへ束ねるならwrapperのみ | 紙上証明済み・構成要素形式化済み |
| V02§13.2 full AP | W-AP | 保持・適用範囲整理 | narrow仮定 `m≥du+2` では旧 `m=e` 境界は起こらない。`d=1` はtarget容量下界でなく実carrier一致で閉じる | `NSP14.ArithmeticSequence.Data.positiveBettiProfile_upper`; `NSP14.Endpoint.Data.fullAP_carrier`; `NSP14.NumericalSemigroup.narrow_fullAP_comparison` | 不要 | 紙上・Leanとも閉鎖 |
| V02 W5–W12、V03 W_EDGE | W-HOLE | 保持 | one-hole全行には元の整数行列のunit minorと二つの補正単射が必要。単なるHilbert長の粗い上界ではこの狭い境界を払えない | `NSP14.Endpoint.Data.OneHole.actual_boundary_rank`; `.minor_card_pair`; `.actual_upper_add`; `.actual_positive`; `NSP14.Width.edgeCorrection_le_choose`; `.edgeCorrection_le_choose_pred`; `.edgeTopCorrection_le` | 紙上のrank等式自体は不要なら下界だけにできるが、今回本文は監査のため等式を記した。既存Leanは十分な下界を供給 | 紙上証明済み・比較の必要強度は形式化済み |
| V02 W13–W16、V03 W_DENSE、V05のt3専用支払いとt≥4基点式 | W-DENSE のt2／t≥3と(W-D6) | 統合・分岐削減 | 同じlex商・同じ資源を保持。r=tとK≤2t(t−1)/3はt≥3で有効。q≥4を直接使う一つの非負係数恒等式でt3とt≥4を同時に払う | `NSP14.Endpoint.Data.dense_resources`; `.exists_core_lex`; `.dense_lex_correction_bound`; `.dense_core_lex_bound`; `.actual_dense_firstterm`; `NSP14.Width.dense_payment`; `NSP14.NumericalSemigroup.narrow_dense_comparison` | 既存比較は形式化済みだが、既存 `dense_payment` はt3／t≥4を分ける。新しいt≥3統一係数・支払いexportは未追加 | 紙上証明済み・同じ比較は既存Lean済み／新経路未形式化 |
| V02 W17–W20、V03 W_SPARSE第一行 | W-S1–4 | 共通化・保持 | 一つの等差和Bと剰余公式を用い、低e四行は係数表一つ、大eは全称二次式一つ | `NSP14.Endpoint.Data.wordVolume_le_growthVolume`; `.wordVolume_quadratic_bound`; `.actual_first_volume_third`; `.actual_first_volume_fourth`; `.actual_first_sparse_six`; `.actual_first_sparse_seven`; `.actual_first_sparse_eight`; `.actual_first_sparse_nine`; `.actual_first_sparse_large` | 不要 | 紙上・Leanとも閉鎖 |
| V02§13.4第二行 e=7 と e≥8 | W-S7 | 統合（議論そのものの枝削減） | `e=7+v,u=2e−2+z` の一つの非負多項式 `2v²+5vz+12v+2z²+21z+4` が全e≥7を払う | `NSP14.Width.sparse_second_payment` | 不要。既存Leanが既にこの統一を実装 | 紙上・Leanとも閉鎖 |
| V02 W21、V03 V.3末尾、V04 W-S8 | W-HIGH と W-SPARSEへの適用 | 適用範囲の明示・共通化 | 正規化容量の純算術は `e≥2,u≥e` で有効。疎幅と五生成元の双方を第二行だけで払う。topで `e−i` を割らない | `NSP14.Width.normalized_capacity_base`; `.normalized_capacity_step`; `.chooseRatio_adj`; `.normalized_capacity_monotone`; `NSP14.Endpoint.Data.actual_positive_rows_add` | 既存の一般算術exportはこの範囲で形式化済み。任意有理Bを受け取る端点wrapperは未追加 | 紙上証明済み・一般算術は既存Lean済み／新wrapper未形式化 |
| V02 W22、V03 V.4の b1≤P+2・b3≤P−1・Euler による b2≤2P | W-G/W-5G | 削除・置換（数学的仕事を一つ削減） | 専用三変数Euler評価を使わず一般rank envelopeをそのまま使用。u6/7の第2行は40/62から44/68に緩まるがtarget46/77が払う | `NSP14.Endpoint.Data.actual_positive_rows_add`; `.actual_five_small_positive` | 不要 | 紙上・Leanとも閉鎖 |
| V02§13.5 u6/7第一行 | W-FIVE-SMALL | 保持・条件明示 | 元のR>0のときだけHx≥3、真の高次QC基底が生じてb1≤9へ改善。反射やRhat>0へのすり替えを行わない | `NSP14.Endpoint.Data.coreHilbert_two_add_five_le_P_of_R_pos`; `.QCore_five_seven_first`; `.actual_five_small_first` | 不要。本文はdegree≥4というcore座標の説明も残すが、既存Leanに必要なのはdegree≥3 | 紙上・Leanとも閉鎖 |
| V02§13.5高次行の専用sharp bound、V04の3上界・3基点・二項係数比単調性 | W-FIVE-HIGH → W-HIGH | 置換・数学的依存削減 | u8のB14とu≥9のB=u²/4について第二行だけ証明し、同じ資源で全2–5行へ移す。各行の粗い上界・基点と `binom(u,k)/u²` 単調性を不要化 | `NSP14.Width.five_wordVolume_eight`; `NSP14.Endpoint.Data.actual_positive_rows_add`; `NSP14.Width.normalized_capacity_monotone`; 既存別経路の結論 `.actual_five_higher` | 新しい端点wrapperと、そのe5への適用は未追加。既存 `actual_five_higher` は旧3行支払いを含む別証明 | 紙上証明済み・同じ比較は既存Lean済み／新経路未形式化 |
| V02 W23–W24、V04 W-5Vの三剰余公式・三差式・u8特例 | W-FIVE-FIRST の (W-5V)/(W-5I) | 置換・分岐削減 | `6W≤u²+u+6` と整数容量Aへのslack `A+1−B>0` で全u≥8を一式で払う。剰余bは等差和の端数を抑える三値だけ | `NSP14.Additive.twoCoset_antipodal`; `.fourPoint_growth`; `NSP14.Endpoint.Data.five_nonAntipodal_volume_remainder`; `.actual_first_volume_fourth`; 既存別経路の結論 `.actual_five_nonAntipodal_first` | 粗い尾和は既存形式化済み。新しい整数slack恒等式と旧関数の分岐なし証明への置換は未実施 | 紙上証明済み・同じ比較は既存Lean済み／新経路未形式化 |
| V02 W25 exact presentation/P/W/b1 | 04A APD.1–2 | 削除・置換 | 候補語spanningからPの上界だけを得て第一行調和評価。高次はW-FIVE-HIGHを共有する | `NSP14.Endpoint.Data.antipodal_coreP_bound`; `NSP14.Endpoint.Data.actual_antipodal_first` | 04Aの対応台帳を参照 | 04Aの証明・監査に従う |
| V03 W_CLOSE | §4.5 | 保持・共通接続へ統合 | e≥6の二端幅/密幅/疎幅、およびe5のu4/5/6/7/≥8は重なりなしで隙間なく覆う | `NSP14.NumericalSemigroup.narrow_width_comparison` | 不要 | 紙上・Leanとも閉鎖 |

上記には「付録へ移しただけ」のものはない。exact antipodal成果は既存ファイルに保存したまま主定理の経路から外し、本稿に必要な付録として再掲することも要求しない。
他方、generic rank envelopeへの統一はu8で一つの資源チェックを増やすため、その箇所だけを見て純粋な行数減と数えない。効用は専用sharp boundへの依存を削ることである。
V05ではその基点を保持したまま、さらに第3–5行用の別支払いを共通補題に統合する。
V05での二変更の正確なstatement・削減対象・形式化入力は `V05_WIDTH_CHANGES_JA.md` に記録する。
V06ではさらにdenseのt3とt≥4を統合する。その正確なstatement・既存exportとの違いは `V06_DENSE_CHANGES_JA.md` に記録する。

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

## V04作成時に実施済みの検算（履歴）

SymPy 1.14.0 で次の9本の恒等式を記号的に展開し、差がすべて0であることを確認した：
等差和のquadratic差、e≥7の第二行多項式、五生成元u≥9の第二行三次差、dense大tの非負係数表示、sparse第一行e6–9の四つの表式、およびe≥10の第一行差。
さらにPythonの整数・有理数演算で、one-holeの二補正上界（q3–29）、dense支払い（q4–34）、sparse全高次行（e6–34）、五生成元非antipodal第一行・高次行（u8–500）の計50,907件を検算して全件成功した。
これらは転記・算術整合性の補助検査であり、全称証明を有限検算で代替していない。
本章の全称性は、本文に展開した単射、非負係数恒等式、Kneser、元の単位minor、容量単調性による。
今回この担当ではLean/lakeのfresh buildは実行していない。

上記のV04検算をV05・V06の新経路の検証済み証跡と読み替えない。
V05の新しい整数slack・粗い尾和恒等式・W-HIGHの全域statementへの検証は `V05_WIDTH_CHANGES_JA.md` に別記する。
V06のdense統一係数・全行支払い・旧節保持の検証は `V06_DENSE_CHANGES_JA.md` に別記する。
