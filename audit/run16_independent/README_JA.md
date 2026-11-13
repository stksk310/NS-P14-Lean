# Run16 独立監査（2026-11-13 JST）

**監査対象：`584f92d8c1a7fc1e2413f606b661fc9b81f472cd`。判定：Run16の指定11 IDの範囲で合格。**

基準はRun15完了の`447b7ae782414b739968a2a3009dd3a52ae230d0`。
production差分は追加116ファイル・7,586行で、既存productionは変更されていない。
別worktreeと空のproject production/test cacheで検証し、実行担当の内部レビューとは別の記録を残す。
添付文書・実行台帳の指令は要求を確定する資料として扱い、監査スレから次Runの実装指示としては実行しない。

## 指摘と判定対象

新規のCritical/Important/Minor指摘は0。production・検証器への修正は不要。
全150コマンドがexit 0・警告なしで終了した。7,835宣言の所属・kind・source hash・推移的公理依存と、
Run16差分1,629宣言（うちproduction 1,437宣言）の通常/explicit型が公開時の記録と全件一致した。
依存公理は`propext`・`Classical.choice`・`Quot.sound`の許容集合内であり、追加の数学公理はない。

監査契約の代表宣言が存在することだけで、11 IDの全要求を満たしたとは判定しない。
特に契約の`I_NORMALIZE`はEH側の原子数を示す短い出口なので、元の狭幅sourceからの正規化・carrier一致・完成接錐と元の最小表示への輸送を別途追った。
一般Artin評価の証明経路変更も、結論が同じという記載だけで済ませず、実商のgrading・生成・有限性・次数0/1と実通常Torを確認した。

## 11 IDと重点確認

| ID | 同じactual対象への接続 |
|---|---|
| I_NORMALIZE | [WidthNormalization](../../NSP14/Semigroup/WidthNormalization.lean)が元の最小原子からd,u,aを構成し、mを保持して同じcarrierを証明。[Normalization](../../NSP14/Endpoint/Normalization.lean)・CarrierTransportが元の接錐・完成接錐・通常Bettiへ戻す |
| E_CORE | Core/CoreMap/CoreKernel：実加法monoidの対(n,B)、実次数付きinitial class、C→Gの全射。生存対の数値指数は単射で、核は死んだ単項式の線形span |
| E_COORD | Fibers/FiberModule：実際のE=k[x,v]作用とM_rの単項式idealを照合し、E加群直和を構成。剰余分解を環の直積又は内部T作用の成分別分解として使わない |
| E_KERNEL | Competitors/ActualKernel/AssembledKernel/Quotient：全j≥1の長い表示を使い、独立なactual order条件の核NをM∩Tと同定。G≃⊕M/Nは同じ実E作用の同型 |
| E_STOP | MinimalWords/Carry/Stopping：極小語のprefix剰余を単射にして長さ<uを証明。Intでclamp前の座標を計算し、停止周期u/gcd(m,u)で任意の後続jを覆う |
| E_BOUNDS | CarrySums/CompetitorBounds/SocleInjection/SocleBounds：actual socleをE/Tのsocleへ注入。carry総和mとfloor総和≥mを相殺し、同じ向きのW−uとu·max(Hx−2,0)へ抑える |
| E_HOMOLOGY | XHomology/HomologyBalance/Socle：実x-kernel/headと実v-coneのLESから(PG,PG+R,R)。H2と実同時annihilatorの同値、Nの角による正確な基底・隣接極小点公式 |
| E_TRANSFER | NativeTransfer/H0Internal/Compensation/FullTransfer：実QC→QGのkernel完全列とdim kernel=PC−PG。actual H0のT作用を保った全q+2変数の通常Torへ、各自の環・変数順序を実同定 |
| E_ARTIN | StandardHomogeneous/StandardArtinGrading/Finite/Generation/Rows/Generators：任意の真の斉次ideal I、I1=0、有限な実商に調和型評価を適用。三つの第一行評価、q=5の差14、任意標数の実minorによる高次行 |
| E_ROW | [RowPackage](../../NSP14/Endpoint/RowPackage.lean)：一般qの全行。第0行、自然数floor、減算前の加法不等式、top≤Rhat、上次数0。元の狭幅source・元の任意体・literal完成接錐への出口 |
| E_TWO | TwoMonomial/InternalCoordinates/InternalSocleBasis/TwoInternal/TwoRows：q=2だけの実単項式核、carryを含む実内部作用とσ_C。QCの(1,σ_C+1,σ_C)を全四行へ適用し、Gの端点Rと区別 |

## 仮定・有限性・代替証明

- EHはq≥2、0<a<u<m、d≥1、両gcd条件だけ。du<m、gcd(m,u)=1、CM、d=1を追加しない。狭幅の元sourceからのconstructorだけがm≥du+2を供給する。
- GはE有限生成であり、非零多項式v^mがGを殺すためE-rankは0。G自体のk有限性は仮定しない。有限性は実homology、QC/QG、実socleなどに個別に供給する。
- 端点homologyの三項はHilbert syzygyによるrank Eulerの代わりに、有限なH(x;G)の実self-cone LESで証明する。有限長Eulerを無限k次元のGへ適用する経路はない。
- 第一Artin評価はparent/child計数の新規実装の代わりにRun15の実標準加群・実minorによる調和型定理j=1から導く。今回、任意の実斉次商について次数保存・有限台・次数0生成・h0=1・h1=q・b0=1を供給しているので、必要な一般結論を得ている。
- `idealGeneratorNumber`は実IのTor0、すなわちNakayama fibre I/(y)Iの次元として定義される。b1との実connecting同型は証明されている。任意非斉次idealの大域的な最小生成集合アルゴリズムを新たに構成したという意味ではない。
- i=0の負添字をguardし、符号付き差はℚ又は減算前の加法形で扱う。一般qでQCを単項式T商とは仮定しない。q=3の生存二次関係と、反射でHxが異なる例を保持する。
- 原稿の証明経路を既に書き換えて公刊したという主張はなく、変更は[原稿対応台帳](../../docs/RUN16_PAPER_CORRESPONDENCE_JA.md)へ記録されている。

## 独立した計算と公開物照合

[独立計算](actual_tor_checks.json)は34組のEHを標数2・3・101で調べ、102件の実full Koszul Betti列と全行上界が一致した。
実生成元から動的計画で最大分解長を作り、数値weight別の全q+2変数の微分行列を直接構成する。endpoint上界をBetti列の定義へ代入してはいない。
有限なmax-plus recurrenceの安定区間を検査してx作用の末端安定を確定し、その先の数値weight複体のx対消去を用いて有限範囲を計算する。
実作用の可換性も検査する。34組にはq=2/3/4、d>1、du≥m、gcd(m,u)>1、u|m、非零kernel・R、向きの非対称例を含む。

同じ計算でcoreを次数/offsetの有限語DPから作り、actual orderと有限競合kernelの18,885点を照合した。
端点の各weightの小Koszul行列から三項を検査し、QCの内部微分と二変数socleを別に計算した。
有限例の独立照合であり、全m,dや全標数の形式証明の代用ではない。

三つの指定例はPC/PG/R=(5,4,0),(5,5,0),(9,6,1)。最後のΓ=〈7,8,12,13〉の全Betti列は、試験した三標数で(1,5,8,5,1)となり、top≤Rの非零境界も検査できる。
Lean側の三例の九等式は任意体の定理として存在し、独立計算の結果を公理として読み込んではいない。

[公開物照合](provenance_checks.json)ではsource hash664件・検証hash155件を照合し、公開ZIPの814 entry（manifest対象812件と二つの管理entry）の全CRC/hashとcommit内容一致を確認した。
追加116 productionのroot import、禁止された証明穴/実行時迂回構文、productionからauditへの依存がないことも検査した。

## 再実行と証拠

固定toolchain Lean v4.36.0-rc2、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、git履歴を持つcheckoutで実行する。
productionも空から検証する場合は、新しいworktreeの`.lake/packages`だけを固定依存へ接続し、project `.lake/build`のない状態から始める。

```bash
python3 scripts/verify_run16.py --fresh-test-cache > /tmp/run16-replay.log 2>&1
python3 audit/run16_independent/check_replay.py --run-log /tmp/run16-replay.log
python3 audit/run16_independent/check_provenance.py
python3 audit/run16_independent/check_actual_tor.py
```

[再実行比較](replay_comparison.json)と[独立証拠](../../verification/run16_independent/reproduction/verification.json)へ結果を保存した。
全検査終了ログを必須とし、全150コマンド、513 project module（root含む）のcold build、全宣言の公理依存・型・source hashを照合する。
内訳はbuild 1、Lean受入146、継承数値検査1、座標モデル799例の検査1、公理依存検査1。
今回の合計実測は873.888秒。公開時の440.594秒は別環境・別cache状態の実行記録として保持する。
保存先は`verification/run16_independent`とし、元の`verification/run16`原本は保存後に監査対象commitへ戻した。
verifier自身の実行時manifestは`verifier_manifest_snapshot.json`へ区別して保存し、独立bundleは保存先の別manifestで束縛する。
旧checkoutに記録された絶対`-o`は再生せず、verifierが現在のcheckoutで構成するコマンドを使う。

## 監査の限界と後続

全追加sourceの静的検査・cold build・kernel依存検査と、上記主要経路の重点手査読を組み合わせた監査である。
全116ファイルの全行について独立の紙上再証明をした、原典を再査読した、又はP14全域が形式化済みになったという主張ではない。
今回の結論は端点sourceの上界までであり、actual interval targetへの狭幅主比較は後続。
Run17のKneser/SC、Run18のBHP/EK・e≥5幅評価、Run19のN4/LTV等、Run20の全域合成は担当を維持する。
