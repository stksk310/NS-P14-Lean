# Run18 公開指令の独立監査

**判定：指令に対する修正必須の指摘なし。実装監査・Run18完成認証は未実施。**

対象は `plan/run18-lex-width-closure-20261113` の
`131f559a9ad495891f0aab487f969bf91b5a447f`、
[公開指令](../../docs/superpowers/plans/2026-11-13-run18-lex-width-closure-order.md) 全149行。
参照した実装基準は公開 `work` の
`c4fd8153f55bb231aab4168a47c1546888fa7ab0`。
確認した公開headsにRun18の証明実装・検証・完成報告はなく、計画ブランチの差分も指令1ファイルだけだった。
実装済みRun18を合格させたという意味の「監査PASS」ではない。

Critical / Important / Minor：今回の指令レビューの範囲で **0 / 0 / 0**。
六閉鎖IDはいずれも本監査で新たに証明済みとは認定していない。

## 対象と方法

1. 公開heads、計画差分、Run17公開状態、幅側本文V.1–V.4を照合した。
2. Run16/17の実sourceから、正規化、QCの作用、核補償付きtransfer、
   P/R/Hx資源、第一行・高次行、実target、巡回成長の型を読んだ。
3. [InputProbe.lean](InputProbe.lean) を固定Leanで再elaborationした。
   全rootをimportし、汎用の体・元のsource・literal targetのまま3つの名前付き補題を証明した。
   使用入力の通常型・explicit型と5宣言の公理依存を出力した。
4. [check_order.py](check_order.py) を新規作成し、既存checkerを呼ばず、
   exact整数・有理数・記号計算と独立core/Koszul行列モデルを実行した。
5. 元のworkの全3,857追跡ファイルを監査前後でSHA256比較した。変更0。
   過去のverificationやZIPは再生成していない。

実行結果は [結果JSON](numeric_checks.json)、[Leanログ](input_probe.log)、
[監査状態](status.json)、[証跡manifest](MANIFEST.sha256) に保存した。
Pythonは標準ライブラリとSymPy 1.14.0を使用。
Leanは `v4.36.0-rc2`、mathlibは
`139105d28c7685a154cb3093f79edb2e16708099`。

## 各Taskのレビュー結果

| Task | 確認した点 | 判定の範囲 |
|---|---|---|
| 1 | 六IDの元契約固定、物理幅du、任意体、実最小変数列、未監査と未証明の区別 | 指令は明確。RequestedGoalsの実装は未公開 |
| 2 | BHP全graded比較、同じ全Hilbert関数のlex存在、EKの商の行ずれ、単位ideal、正標数 | 契約に数学的な誤りは見つからない。実証明はまだ監査できない |
| 3 | full APのd=1別処理、欠落基底、符号付きrank、負添字、上端補正 | 独立モデル・支払い検査と整合 |
| 4 | q=3の資源とq≥4の閉鎖の区別、prefix、同じlex商、K計数、dense差 | 資源モデル・差の計算と整合 |
| 5 | 尾和、剰余項、e=6–9/≥10、第二行、T_iの全高次行への橋 | 記号恒等式と有限検査が整合 |
| 6 | u=7のR>0限定、床、非antipodal、非unitのt、同じQCのpresentation | 指定式と独立モデルが整合 |
| 7 | 全幅分割、元のSへ戻す接続、i=0/e/e+1、target自身の変数数 | 分割の穴は見つからない。最終閉鎖の実装は未公開 |
| 8 | 過去証跡の保全、全宣言依存、review/snapshot束縛、通常Push | 指令として必要条件がある。未公開verifier/packagerの動作は監査不能 |

## 数学上、実装時にも保持すべき接続

これは新しい欠陥の列挙ではなく、指令に既に含まれる条件の確認である。

* **full AP・d=1**：一般のFmin(u)で払わずsource=literal targetを使う。
  d≥2ならV≥2uの支払いへ進む（指令71行）。
* **QCからG**：`actual_core_endpoint_bound` に実核補償が含まれている。
  別のsourceやQCだけの比較へ置換できない。
  `actual_positive_rows_add` は引き算前の加法形を供給する。
* **dense**：t=2の最小余裕はq=4,i=1で0である。
  単に「十分大きい余裕がある」として境界を削れない。
  q=3は資源補題の範囲であり、dense閉鎖の範囲に混ぜない。
* **疎幅の全行の橋**：u≥e、i<eで
  A_i=C(u,i)/C(e,i) と置くと A_{i+1}/A_i=(u-i)/(e-i)≥1。
  したがって幅増分 i*A_i+i/e はiについて増加する。
  T_i(e)=e-1+i/e と合わせてT_i(u)≥T_2(u)を得る。
  最後の隣接比較i=e-1は分母1であり、i=eで比を作る必要はない。
  これは指令102行の帰納の明示的な読み方である。
* **u=7**：b1≤9はR>0の分岐だけ。R=0ならβ1≤20で処理する。
* **antipodal**：gcd(t,h)=1だけでよく、gcd(t,2h)=1は不要。
  例えばh=5,t=2は独立モデルでも指定presentationと一致する。
  次数n<hの純(y,w)語のoffsetはnt+jh (0≤j≤n)で相異なる。
  より短い語への端点因子分解は、mod hでgcd(t,h)=1を使うと排除できる。
  yz=xw、z²=xv、zw=yv により三つの二次語はQCで消える。
  次数hの純語は端点とzで表示できるので消える。
  この議論を同じQCの作用・基底へ形式的に接続することが必要で、
  今回の有限モデル検査だけではその全称接続を認証していない。

## 独立計算の範囲と結果

すべてPASS。ただし有限検査を全称証明の代替としていない。

* 指定された多項式の記号恒等式14件をexactに確認。
* sparse：6≤e≤40、2e−2≤u≤2e+60、2,205組。
  各2≤i≤eでT_i基点・幅増分・第二行以上の支払い、各48,510比較。
* dense支払い：4≤q≤40、2≤t≤q、全1≤i≤q+2、22,866比較。
* dense実core資源：3≤q≤5、0≤t≤qの生成条件を満たす623 profile。
  語長、元の向きのHx、W=q+1+2t、P≤Wを検査。
* edge：5≤u≤9の全欠落、30 profile。
  整数offsetのnBからQC基底・実内部作用を組み、Q/F2/F3で別々にrank計算。
  内部欠落の450 rank比較・450 Betti比較・450 T_i比較、
  全欠落の660 transfer支払い比較。i=q+1/q+2を含む。
* antipodal：4≤h≤9、1≤t<h、gcd(t,h)=1の全24 profile。
  実offsetからQC基底/P/Wを計算し、Q/F2/F3で72件のb1=h+4を検査。
* 五生成元の小幅表、8≤u≤300のB3・床・高次行、
  4≤h≤100のantipodal第一行差を確認。

rankが異標数でも同じ値だったという実験を、任意標数の証明には使っていない。
edgeの±1 minor、antipodalの一般presentationは将来のLean証明の義務として残る。

## 既存APIと、まだ必要な基盤

[Lean確認](InputProbe.lean) は実際の以下の入口を使用・検査した。

* `Endpoint.Data.actual_core_endpoint_bound`：q内部変数とq+2全変数、実Rを保持。
* `NumericalSemigroup.endpointData_narrow`：d*u+2≤mを供給。
* `interval_completed_betti_lower`：幅min(width,m−1)の下界からliteral completionへ接続。
* `QCore_internal_basis`、`coreP_le_wordVolume`、`actualR_le_volume`、`actualR_le_height`。
* `QCore_first_harmonic`、`QCore_first_third`、`QCore_first_fourth`。
* `wordVolume_tail`、`wordVolume_growth_bound`、`fourPoint_growth`、`gradedBetti_total`。

このうち公理依存を今回抽出したのは、3つのprobe定理と
`wordVolume_growth_bound`、`fourPoint_growth`の5宣言である。
いずれも `propext`・`Classical.choice`・`Quot.sound` のみ。
Run17全体の独立監査やRun18全宣言監査を実施したとは表示しない。

固定mathlib/projectの関連sourceを再検索したが、正確なBHP/EKの既存exportは見つけていない。
検索だけでライブラリ内の不存在を形式的に証明したわけではない。
Task 2は一般斉次商のlex存在・任意標数の実Tor比較・EKの解消を含む大きな新規基盤で、
他Taskの数値支払いが通ることだけでは閉じない。
run数を守るためにこの契約を弱める必要はなく、指令147行の正直な未完記録を適用すべきである。

## 監査できなかったもの

Run18の `RequestedGoals.lean`、六IDの証明export、consumer、全fixture、
新規productionのcold build、全宣言の型/公理依存、verifier/packagerのguard、
完成ZIPは公開されていないため未監査。
今回は新たなRun18証明がないので、既存全回帰を再実行してRun18完成の根拠にはしていない。
原典BHP/EKの全証明を独立に再構成した監査でもない。

再現：元のwork基準で `lake env lean <このディレクトリ>/InputProbe.lean`、
Python環境で `python check_order.py`。両方とも既存証跡を上書きしない。
auditブランチの追加ファイルは `audit/run18_order_independent/` のみ。
