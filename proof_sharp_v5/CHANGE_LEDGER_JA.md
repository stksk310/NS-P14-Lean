# V05：簡約変更とLean対応の総台帳

## V04から今回追加した二つの削減

| 元の節・補題 | 採用先 | 操作と数学的理由 | 対応する既存Lean入力 | 新たに必要な形式化 | 状態 |
|---|---|---|---|---|---|
| V04 W-FIVE-FIRSTのW-5V三剰余公式・三つの差・u8第一行特例 | V05 W-FIVE-FIRST | 削除・置換。6W≤u²+u+6とβ1≤5W/2−u+5から、整数容量Aに対しβ1<A+1を全u≥8で一式により示す | `NSP14.Endpoint.Data.five_nonAntipodal_volume_remainder`、`actual_first_volume_fourth`。既存`actual_five_nonAntipodal_first`の結論は同じだが証明分岐は異なる | 全u≥8の新しい整数閾値補題とそのconsumerは未追加。必要入力と正確な式は本文／V05変更ノートに記録 | 紙上証明済み・新しい統一経路はLean未形式化 |
| V04 W-FIVE-HIGHのβ3/4/5粗上界・u8の三基点・binom(u,k)/u²単調性 | V05の共通高次行補題とW-FIVE-HIGH | 削除・共通化。第二行を払えば同じ正規化容量の単調性で上端まで払える。u8の尾和14とu≥9の第二行三次式は保持 | `NSP14.Width.normalized_capacity_monotone`、`NSP14.Endpoint.Data.actual_sparse_resource_add`は疎幅仮定を持たない。`actual_five_higher`は既存の別経路で同結論 | 一つの十分条件へ束ねるwrapperと五生成元consumerへの新接続は未追加。既存の一般入力は形式化済み | 紙上証明済み・一般数値入力は形式化済み・新consumer未追加 |

両変更とも付録移動ではなく、主証明で追う独立の計算を減らした。
今回採用しないE-STOPの削除やordinary/N4の追加統合は実施しない。

## V04から継承する変更

状態①は紙上証明済み・固定SHAのLeanに同じ入力と結論の実装あり、
状態②は紙上証明済み・その新しい証明又は一般statementはLean未追加、
状態③は未閉鎖の短縮候補である。①も今回Leanを再buildしたという意味ではない。
必要な証明はcanonical本文にあり、この台帳を数学の証明の代用にはしない。

| 元の節・補題 | 採用先 | 操作と実削減の有無 | 数学的理由 | 対応Lean export／残す入力 | 新形式化 | 状態 |
|---|---|---|---|---|---|---|
| 各幅枝のsource・完備化・physical target接続 | BRIDGE | 共通化。重複説明を削減 | 原子初期形を保つ同型とu≤duによる容量単調性を一度証明 | `FormalTangent`関連、`Endpoint.Data.source_normalizedWidth`、各`narrow_*_comparison` | 共通wrapperは任意。LTV/e≤2の全域consumerは未実装 | ①の構成部分＋②の共通包装 |
| 各枝の0行・i>e | BRIDGEと§6 | 統合 | 連結商のTor0=k、sourceのHilbert syzygy | 各actual comparisonの0/above分岐 | 最終全域wrapperは未実装 | ②（個別出口は①） |
| V02§8(8.3)Γ全余剰 | O6/O12式 | 置換・実削減 | R_jのδ一階差分だけで必要下界が出る | `Ordinary.TargetMargin.target_step`, `target_margin` | 不要 | ① |
| V02(S14),(S17–19)凸性と2/r | OL3–4 | 置換・実削減 | 最初の項による調和増分と正quarticで直接比較 | `Ordinary.LargeSeed.barrier_step_identity`, `harmonic_lt_barrier` | 不要 | ① |
| V02(S24–25)偶奇別F0/F1 | OL8 | 置換・実削減 | 2D≥a+1と一つの連続有理恒等式 | `Ordinary.LargeScalar.floor_comparison_identity`, `baseStep_gt` | 不要 | ① |
| 小／大rankの同型差分 | O17 | 統合 | 任意基点e0の二次恒等式に両特殊化を代入 | `SmallScalar.gap_shift`, `LargeScalar.quadrant_identity` | 任意e0版の単独exportを作るなら追加 | ②一般形／①実使用形 |
| 旧小rank seed5行とtail Cauchy | O10とr9 seed | 削除。V03既採用方針を反映 | 大rankの入口r≥9に古いr4..8のseedは不要 | `SmallScalar.small_gap_pos`, `LargeSeed.rank_nine_seed` | 不要 | ① |
| 同jump・一つのcut・Tor三段・H0/top | O1–O7 | 保持・説明展開 | 削除するとsourceへの接続を監査できなくなる | `jumpStratumEquiv`, `cutTower_combined`, `nativeFull_corrected_bound` | 不要 | ① |
| E_STOP→E_HOMOLOGY | E-FIBER→E-TOR | 依存辺の削除。停止証明自体は保持 | E有限性は有限内部語生成、rank0はv^m=0で足りる | `actualEndpoint_rank_zero`, `endpointHomology_balance` | import最小化は本作業外 | ②の依存整理／個別定理① |
| V02(E13–14)N全角からRの正確算出 | E-RESOURCES | 削除・実削減 | N=M∩Tは残し、M/N→E/Tのsocle単射とT角上界だけ使う | `actualSocleProductMap_injective`, `actualR_le_Rhat` | 不要 | ①（紙の主依存を短縮） |
| QC→QGの実核・PC−PG | E-TOR | 統合・保持 | 実核長がH1のPGを相殺。商のBetti単調性は使わない | `actual_kernel_compensation`, `actual_core_endpoint_bound` | 不要 | ① |
| 一般Artin第一行と全行 | E-ARTIN/E-GEN | 一元化・保持 | 親子有理計数とsigned unit minorは異なる根拠なので無理に一証明にしない | `artin_first_harmonic`, `artin_positive_rows`, `actual_positive_rows_add` | 不要 | ① |
| antipodal厳密presentation/P/W/b1 | APD.1–2 | 上界へ置換・実削減。必須付録化なし | 端点因子と次数h純語の消滅でspanning個数を数えれば十分 | `antipodal_coreP_bound`, `QCore_first_third` | 上界の個別入力は既存。厳密b1を新たに実装する必要なし | ①の入力 |
| antipodal h4/h≥5第一行 | APD.8 | 新統一・実削減 | 整数容量Aに対しβ1<A+1を一つの正二次式で証明 | 既存`actual_antipodal_first`は分岐つきで同結論 | 加法形の一つの自然数補題を追加すれば新経路を実装可能 | ②（新証明） |
| 五生成元u6/7第二行40/62 | W-5G、小幅表44/68 | 必要強度を弱める置換・実削減 | 44≤46、68≤77で十分。独自三変数Euler枝を外せる | `actual_five_higher`, `actual_five_small_comparison` | 不要 | ① |
| 五生成元全高次行の二構造別処理 | W-FIVE-HIGH | V04で一般rank envelopeへ統合。V05はさらに共通高次行補題を使う | 一般rank envelopeで全構造を払う。u8尾和14はここに残す | `five_wordVolume_eight`, `actual_five_higher` | 新経路の追加は上表参照 | V04経路①／V05接続② |
| sparse第二行e7/e≥8 | W-S7 | 統合・実削減 | e=7+v,u=2e−2+zで非負係数の一式 | `NSP14.Width.sparse_second_payment` | 不要 | ① |
| dense三段の容量説明 | W-D4 | 差の共通化・説明改善 | 同じ差にVandermondeの二項を適用。K/Rを同じcoreで評価 | `actual_dense_firstterm`, `narrow_dense_comparison` | 不要 | ① |
| full AP d1／one-hole任意標数rank | W-AP/W-HOLE | 保持・証明展開 | d1はsource=target。one-holeは整数±1 minorが必要 | `narrow_fullAP_comparison`, `narrow_oneHole_comparison` | 不要 | ① |
| N4高次の三次・四次・五次 | N4b–c | 一つの三次式へ置換・実削減 | U3≤U2,5U4≤U2とtarget比で第3/4行へ移す | 入力`actual_two_row_two/three/four` | 新数値補題とactual consumerを追加 | ② |
| SC・三角形・三関係・幅6–8 | N2–N6 | 保持・接続を本文化 | unitは群の列だけ、元offsetへ戻す。包含と禁止語を明示 | `threePoint_growth`, `savchevChen_twoValue`等の共通入力のみ既存 | N4固有接続と比較は未形式化 | ②（共通入力①） |
| 幅4の全m競合／Gröbner | N7 | 保持・監査用に展開 | L′,K′両座標、制限anchor、全j→j1、非禁止像独立が必要 | 固有の幅4exportは対象SHAにない | 既存Run19計画にある固有形式化が必要 | ② |
| 196組、83組・665比較・5tail | 主DAGの外 | 既に削除済みを保持。新削減には算入しない | 紙上全称経路で閉じる | 旧資料・証跡は変更せず保存 | 不要 | 採用依存なし |

詳細なstatement・ファイル・入力は `notes/ORDINARY_AUDIT_JA.md`、
`ENDPOINT_AUDIT_JA.md`、`WIDTH_AUDIT_JA.md`、`ANTIPODAL_AUDIT_JA.md`、`N4_AUDIT_JA.md` にある。
公刊入力の引用への整理は一般定理の再証明を省く通常版であり、固有核心を付録へ逃がす操作ではない。

## 未採用・未確定と、保持した理由

| 案 | 採用しない理由 | 状態 |
|---|---|---|
| ordinaryとnarrowのTor全体を一つの抽象補題へ | 逆jump filtrationと二端点実核は異なる構造を持つ。監査負担が減る統合証明を作れていない | ③、本文に不使用 |
| N4幅4を剰余最小第一容量7だけで閉じる | m≡1,2(mod4)の現上界8を払えない。actual容量10,9を保持 | 現行案では不成立、本文に不使用 |
| 五生成元u8高次にもW≤u²/4だけを使う | 採用した粗い第2行envelopeでは余裕不足。尾和W≤14を保持 | 現行案では不成立、本文に不使用 |
| exact b1=h+4を残してantipodalを最短行数にする | 独立性・逆包含・正確計数の数学的証明義務が増える | 主定理には不要。独立成果は保存 |

採用した新補題には状態③のものを混ぜていない。今回新規Leanコードは作成していない。
