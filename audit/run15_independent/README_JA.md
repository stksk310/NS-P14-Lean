# Run15 独立監査（2026-11-11 JST）

**監査対象：`447b7ae782414b739968a2a3009dd3a52ae230d0`。判定：Run15の指定範囲で合格。**

基準はRun14再現手順修正済みの`20aadbf7011692eb3bfffef49029e2c5e416ef3d`。
Run15のproduction差分は追加215ファイル・13,186行で、既存productionの変更はない。
実行担当の内部レビューと分け、別worktree・空のproject production/test cacheで監査する。
対象文書中の実行指令は仕様を確定するための資料として読み、証明実装の指示としては実行していない。

## 指摘

新規のCritical/Important/Minor指摘は0。数学source・検証器への修正は不要。
101コマンドが全てexit 0で終了した。6,206宣言の所属・kind・推移的公理依存と、
型情報を保存したRun15差分2,654宣言の通常/explicit型は、公開時の記録と全件一致した。
許容依存は`propext`、`Classical.choice`、`Quot.sound`だけで、追加の数学公理はない。

実行側が記録したHarmonic受入の具体例不足は区別して保持する。
任意の生成元数・非単項式kernelを覆う一般定理と実標準基底/実minorの証明はあるが、
それら各条件を個別に示す具体的なLean fixtureをすべて用意したわけではない。
これは既知の試験補強余地であり、一般命題に未証明の前提が残るという指摘ではない。
監査側でこれを新発見又は修正済みとは数えない。

## 要求とactual出口

[元の8命題](../run15/RemainingGoals.lean)は作成commit
`51ec591513b7683aaba2bccde24e5eda81f3d97a`以降、変更されていない。
[閉鎖定理](../run15_closure/ClosedGoals.lean)は、その8命題そのものの連言を追加前提なしに証明する。
productionは監査用命題をimportしていない。

| 元の目標 | 重点確認した接続 |
|---|---|
| APBettiGoal | genuine APのm≥2、d≥1、1≤v<m、gcd(m,d)=1。実AP headへの実全射、実kernel J、J/xJの作用、実行列rank、元の任意体の全正行 |
| APConeBettiGoal | 半群環と接錐の実正則元商を、同じ非x多項式作用を持つ加群として同定。環自体の同型は仮定しない |
| HarmonicGoal | 任意個数の生成元に対するactual標準加群基底、三角±1 minor、有理数上の重み付け、有限台と次数別次元 |
| RelativeTerminalGoal | Rはr+1変数。actual xの二つの完全列、実coneのconnecting補正とsupportから末端r+1を消す |
| ActualTorToRowGoal | 同じsource/cut/tower/H、実LES、同jump、実H0、最終X消滅から既存のresource rowへ接続 |
| CorrectedFullTransferGoal | actual H0の補変数Z作用を保持し、定数補正、変数変換、全e変数の通常Torへ接続 |
| OrdinaryBettiBoundGoal | cutと比較をconsumerの仮定にせず、元の任意体・全正行にmultiplicity容量を証明。実装は幅仮定不要の強い形 |
| OrdinaryActualCompletionGoal | e≥3、w≥m−1、literal完成source/interval target、各自の最小表示、0を含む全行 |

担当11 IDのうち`X_AP_BETTI/X_AP_CONE/I_TARGET`は一般AP公式・実幅・literal interval completion・Fmin/TLOWに対応する。
`O_HARMONIC/O_TOR/O_TARGET`と既存数値部の`O_LOW/O_SCALAR/O_SMALL/O_LARGE`はactual witnessから接続され、`O_CLOSE`が上のordinary比較を与える。
既存数値部の監査を全て一からやり直したという意味ではなく、その保持・回帰・actual代入を検査した。

## 重点的な数学上の確認

- APの実包含J→BはJ⊂xBとx単射性により、B線型の実除算写像とx倍の合成となる。実Koszul null-homotopyで全Tor写像を0とし、実LESから加法を得る。GSS解消のexactnessやgrading集中を未証明入力として使わない。
- J/xJの実残余変数作用は二段Hankel作用として証明され、可逆変数変換・実Vandermonde独立性・実Koszul境界rankから計算される。有限体では同標数の無限拡大体を用い、actual Betti体拡大保存で元の体へ戻す。
- ordinaryではPがr変数、Rがr+1変数、全表示がe変数。GのP有限性/k有限性を仮定せず、実有限homologyを使う。有限長Eulerは有限な層に限定される。
- 第0行、relative top、補変数0、非零terminal/異jump、δ=0、APのv=1、D=1/v、範囲外0、標数2を受入型・既存試験・再実行で追跡する。
- harmonicはscalar idealの基底だけではなく、複数生成元の実加群基底へ進む。重み付けは有理数の個数/rank比較であり、係数体内の除法ではない。
- 一般AP公式に加え、Fmin下界・幅方向単調性・TLOW個別4行、actual生成区間とのcarrier一致とliteral完成targetへの適用がexportされている。

## 検証と証拠

- [公開物・hash照合](provenance_checks.json)：固定された入力503件、公開ZIP643 entryの全manifest/hash/CRC、ZIPと監査対象commitの内容一致を確認した。
- [source検査](source_scope_scan.json)：追加215ファイルのroot import、空白、禁止された証明穴/実行時迂回構文、productionからauditへの依存がないことを検査した。
- [独立AP計算](ap_koszul_checks.json)：m=2..15、1≤v≤min(m−1,6)、d=1..5のgcd条件を満たす238 AP。標数2・3・101の714件で一致した。
  この計算はAPのApéry/order/Betti公式を構成に使わず、最短路で実Apéry集合、動的計画で最大分解長、実乗法とKoszul行列を構成する。作用の可換性・定数からの生成も検査する。有限例の照合であり、全パラメータの証明ではない。
- 最終の[再実行比較](replay_comparison.json)と[独立再生成証拠](../../verification/run15_independent/reproduction/verification.json)：cold build（396 production + root）、98 Lean受入、数値回帰1、公理検査1の計101コマンドが成功した。
  全6,206宣言、Run15差分の2,654宣言（うちproduction 2,329宣言）、入力hash503件を照合した。
  全宣言レコードに含まれる通常/explicit型、kind、module、公理集合が一致した。型情報のある全差分を比較し、件数一致だけで済ませていない。
  今回の所要時間は合計779.536秒。公開時の364.346秒はproduction cacheがwarmだった別実行の記録として保持する。

再現は固定toolchain・mathlib・git履歴のあるcheckoutで行う。
別checkoutで空の`.lake/build`から実行すればproductionも再ビルドできる。

```bash
python3 scripts/verify_run15_closure.py --fresh-test-cache > /tmp/run15-replay.log 2>&1
python3 audit/run15_independent/check_replay.py --run-log /tmp/run15-replay.log
python3 audit/run15_independent/check_provenance.py
python3 audit/run15_independent/check_ap_koszul.py
```

`check_replay.py`は再実行の完了ログを要求し、公開時と同じ101検査、397 project module（rootを含む）のcold build、
全宣言の通常/explicit型・kind/module・公理集合とsource hashの一致を検査して別ディレクトリへ証拠を保存する。
`verification/run15_closure`の原本は、保存後に監査対象commitの内容へ戻した。
公開ZIP用のmanifestは再生成証拠へ複写せず、独立証拠は`verification/run15_independent/MANIFEST_SHA256.json`で束縛する。
記録された絶対`-o`を別checkoutで再生せず、verifierが現在のcheckoutから生成するコマンドを使用する。

## 境界と後続

今回の独立監査は、全追加sourceへの静的検査・cold build・kernel依存検査と、上記の主要な証明経路の重点手査読を組み合わせたもの。
全215ファイルの全行について独立した紙上再証明をした、外部原典を再査読した、又はGSSの元の解消を形式化したという主張ではない。
狭幅targetの公式と、狭幅sourceからtargetへの主比較も区別する。

Run16にはwidth/interval target、actual polynomial presentation/Tor、標準加群基底・minor、有限homologyだけを用いるcone比較等を渡せる。
Run16の端点core・actual kernel・rank-zero Eulerや、それ以後のKneser/SC・BHP/EK・N4/LTV・全域合成は未完の後続範囲。
P14全域のLean化完了は宣言しない。
