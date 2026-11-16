# V06 Lean経路同期：原稿対応・変更台帳

取得baseは **a7504eea25f02728d1be6cd0082e8484d639dbe2**。今回の指令は既存 `docs/superpowers/specs/2026-11-15-v06-alignment-order-input.txt` とbyte一致。V06原稿・ZIPはbaseに収録済みで、既存Leanに対する誤り修正ではなく主経路の同期である。既存Run18 COMPLETEと全六契約を保存する。この台帳自体は実行成功の認証ではなく、新規固定proof commitに結び付いたverification/review/packageで認証する。

## 五つの接続

| V06の変更 | 新補題／変更した証明 | actual consumer | 保存した凍結受入への接続 |
| --- | --- | --- | --- |
| endpoint E-HEIGHT | `competitorMin_height` は全j witnessの長い側点を極小化し `forbiddenStart_le` / `forbiddenStart_height` から直接得る。`competitor_zero_column` はj=uの高さと`coreHeight_le`を使う。 | 元の`competitorFiber`、`actualDeadFiber_eq_inter`、`actualR_le_height` / Rhat / RowPackage・FullTransfer | 同じ向きのactual R、PC/PG補償を通じ、既存W_FIVE/W_SPARSE/W_EDGE/W_DENSE/W_CLOSEへ。元の核定義は不変。 |
| antipodal第一行 | `Width.antipodal_integer_payment`。6b+7h≤11h²+30から、整数性によりb≤C(2h,2)+1。h=4から統一。 | `Endpoint.Data.actual_antipodal_first` | `narrow_five_large_comparison` → `narrow_five_comparison` → W_FIVE/W_CLOSE |
| non-antipodal第一行 | `Width.nonAntipodal_integer_payment`。12b+7u≤5u²+90からb≤C(u,2)+1。u≥8を統一。 | `Endpoint.Data.actual_five_nonAntipodal_first` | `narrow_five_nonAntipodal_comparison` → W_FIVE/W_CLOSE |
| 高次行共通化 | `Width.higher_capacity_from_second`、`Data.actual_resource_envelope_add`、`Data.actual_higher_from_second`。同じ有理Bで二資源を包絡し第二行を支払う。 | `Data.actual_five_higher` / `Data.actual_sparse_higher` | five/sparseの各全行comparison → W_FIVE/W_SPARSE/W_CLOSE |
| dense二枝 | `Data.dense_core_lex_bound_two_branch`、`Width.dense_gamma_nonneg` / `dense_coeff_ge_three` / `dense_payment_ge_three`、`dense_payment_two` | `Data.actual_dense_firstterm`が一つのKを受けt=2／t≥3へ直接分岐 | `narrow_dense_firstterm` → `narrow_dense_comparison` → W_DENSE/W_CLOSE |

## Endpoint：全jと計算枝の区別

Carryの既存`carry_epsilon_lower` / `floor_jm_ge` / `forbiddenStart_height`を使い、新しいceilingライブラリは作らない。`competitorMin_finite`は既存の二変数antichain有限性をそのまま使う。全jからなる集合を有限個jの核へ置換しない。gcd(m,u)=1を追加しない。

`CarrySums`はStoppingからActualKernelへのimport差替え、Volumeは保持。`CompetitorBounds`の極小点高さは旧停止に依存しない。`FiniteSocleBounds`の純v冪は全j評価のj=uを使う。`FiniteCompetitors`にStoppingの明示importを加え、従来の停止上限による有限計算APIを保存する。

個別importの根はRowPackage、SocleBounds、Width.Closure。umbrella NSP14は意図的に旧Stoppingも保持するため、主経路判定には用いない。`scripts/check_v06_routes.py`は個別import閉包と名前付きproof本文の直接参照を記録する。推移的数学の確認は独立ソースレビューが補い、公理検査とは分離する。

## 整数slackと強い独立結果の保存

新IntegerPaymentの計算はℚ上で行い、仮定の整数bが次の整数A+1へ届かないことを示す。h−4/u−8はℚ上の通常差でありNat飽和減算を式の途中で代用しない。体内除算は使わない。

antipodalのactual第一行は`antipodal_coreP_bound`、`QCore_first_third`、実kernel補償、R+2h≤W、粗いW≤h²から仮定を導く。h=4専用のW≤14や厳密P/W、presentation、Betti輸送は前提にしない。non-antipodalは既存6W≤u²+u+6と第四調和評価を使い、u=8/9/10/11専用払い戻しを外す。既存の厳密antipodal成果や余りmod3の算術定理は削除しない。

## 同じBを使う高次行

第二行のactual β₂だけから一般行は推論しない。`coreP≤B`と`Rhat+u≤B`を同時に仮定し、actual加法形
`β_i+u*C(e−1,i−1)+C(e−1,i+1)≤B*C(e,i)`
を証明する。同じBの第二行容量を`normalized_capacity_monotone`へ渡す。割るのはi≤eによって正なC(e,i)だけであり、e−iでは割らない。

fiveのu=8ではB=14、第二行包絡104≤112（加法形140≤148）を使う。u≥9ではB=u²/4。z=u−9に相当するℚの差について容量の差を `(2z³+33z²+136z+33)/6>0` と証明した。i>5のsource消滅も保存する。旧choose_quadratic_step/from_eightは公開結果として残し、新actual higherからは呼ばない。sparseは同じWと既存`sparse_second_payment`を使う。新共通wrapperはfive/sparseのhigherや最終comparisonをimportしない。

## 同じLとKを使うdense

helperはt≤qという旧範囲（t=0/1を含む）を狭めず、一つの∃Kの内部で全core行と`t=2→K≤2`、`3≤t→3K≤2t(t−1)`を同時に返す。t=2はr=3、t≥3はr=t。旧`dense_core_lex_bound`は新helperから従来条件を導く互換wrapperにした。

新係数のγ≥0はq−4、t−3、q−tの非負性から証明する。新paymentは旧三枝paymentや旧large_coeffへ戻らず、新係数とVandermonde二項下界を使う。q=4,t=3ではγ=0であり、j=0で等号を許す。最上端j=q+1も二項係数を割らず処理する。q=3の資源は不変。旧`dense_payment` / `dense_large_coeff`の公開型は保存した。

## 変更・認証境界

有限許可リストは `docs/V06_ALIGNMENT_CHANGE_POLICY.json`。変更した既存productionはEndpoint四つとWidth七つの計11ファイル、新productionはIntegerPayment/HigherFromSecondの二つ。新fixture四つとRouteChecks、検証・control・package・routeスクリプト、計画・台帳・引継ぎ・変更規則だけを追加する。umbrellaと二つの既存台帳はprefixを保存して末尾追加する。

旧verifier/checker、凍結acceptance、過去verification/artifact、V06原稿は改変しない。新検証器は改変旧moduleの全公開型をbaseの隔離実行結果と照合し、normal/explicit型とcollectAxiomsを保存する。元Run15–18の受入も含む280コマンドを新規先に写像して再実行し、新fixture・依存・negative controlsを加える。全project cacheを退避してEndpoint下流も再構築するが、固定mathlib cacheは共有する。

対象外はordinary一般export、N4、Run19、全P14合成。今回の完了名は五項目がactual consumerまで閉じたときの **V06_ALIGNMENT_COMPLETE** に限定する。
