# Run18 実装の独立監査 — 2026-11-15

**判定：公開済みPARTIAL成果は監査通過。Run18全体は未完。**

監査対象commitは `58a0f54651916a4f7d6aa2e172d9250d91fd25f4`。
Run18基準は `c4fd8153f55bb231aab4168a47c1546888fa7ab0`、
公開指令は `131f559a9ad495891f0aab487f969bf91b5a447f`。
前回の `audit/run18-order-20261113` は指令だけの監査であり、今回は実装・実証明・公開証跡を対象にした。

**修正必須の指摘：Critical 0 / Important 0 / Minor 0（PARTIALという公開範囲に対して）。**
本番数学sourceの修正は要求しない。未証明の四IDを合格認証したという意味ではない。

## 閉鎖範囲

| ID | 判定 | 実際の証明・残る義務 |
|---|---|---|
| `W_SPARSE` | 閉鎖を確認 | `NSP14.Run18.sparse_closed`。任意体、元のS、e≥6、u≥2e−2、物理狭幅、全Betti行、literal interval completion |
| `W_FIVE` | 閉鎖を確認 | `NSP14.Run18.five_closed`。任意体、元のS、e=5、物理狭幅、全正規化幅・全Betti行、literal interval completion |
| `X_BHP_EK` | 未完 | 一般斉次商の任意標数BHP/Pardue・lex存在・EK本体。Lexの定義と次数piece有限性だけでは閉じない |
| `W_EDGE` | 未完 | full APは完成。q=3,u=5も完成。q≥4,u=q+2の実作用・rankと支払いが残る |
| `W_DENSE` | 未完 | 凍結された`DenseResources`は完成。一つのlex商によるK計数と`DenseClosure`が残る |
| `W_CLOSE` | 未完 | e=5と疎幅以外の分岐を閉じて、元のSの全物理狭幅へ合成する義務が残る |

`RequestedGoals.lean` は初出commit
`cdce65ad0678170b80d6a91e75913d9b39b65f86` から不変。
SHA256は `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`。
両閉鎖定理はこの元のPropを直接証明し、追加比較前提・無限体・特性0・CM性を要求していない。

## 数学sourceのレビュー

新規production 37 module、3,719行を通読し、指令・V03 V.1–V.4・凍結型と照合した。
主要な確認点は次のとおり。

* 正規化前の元のS、同じ係数体、両環自身の最小変数列を保持している。
  targetは`S.intervalCompletion`の完備接錐であり、正規化幅uの仮想targetに置き換えていない。
  `u≤S.width`、物理幅`V=d*u`、完備/代数的接錐の既存同値を通す。
* `FirstResources`、`SparseHigher`はactual QCと核補償済みtransferを使う。
  `P_C=P_G`やR=0を仮定せず、Rhatを使う箇所は元のRの証明済み上界として使う。
* 疎幅の等差和・剰余式・第二行・正規化容量は実証明。
  正分母を確認し、i=eでe−iによる除法を行わない。
  i=0、第一行、高次行、source消滅後を分離し、targetの高い行を0と断定しない。
* denseのprefix単射は同じCoreMinimalと端点factorから導かれている。
  Hxは元の向き。q=3を含む資源の完成とq≥4の全行比較の未完を区別する。
* full APは元のoffset集合から実sourceを識別する。
  d=1はsource/targetのcarrier同一性、d≥2は物理幅による支払いを使う。
* u=7の第一行改善は元のactualR>0の分岐だけ。
  Hxと実QCの高次基底からh2の不足を導き、R=0の場合の評価と混同しない。
* antipodalは`gcd(t,h)=1`だけを使い、`gcd(t,2h)=1`を追加していない。
  実coreの生存点・指数単射・係数ごとのkernelから
  `(YZ,Z²,ZW)+(Y,W)^h`のliteral idealを同定する。
  元の変数像・次数・多項式作用を保つmodule同型・actual Torへの輸送まである。
  群のunitで元の数値半群を取り換えていない。
* u=5の内部欠落は実kernelの5生成元と実Koszul微分の3×3符号付き単位minorを使う。
  対角±1は標数2でも単位。実Eulerと組み合わせて低行を払う。
  端欠落のP上界も元の向きのまま証明している。
* 五生成元の幅4、5、6/7、8以上の両構造という分割は全域を覆う。

## 原稿との相違

次は証明の欠落ではなく、同じ凍結結論を与える証明済みの別経路である。
`docs/RUN18_PAPER_CORRESPONDENCE_JA.md`にも記録されていることを確認した。

1. 第二行のe=7/e≥8分岐をe=7+vの一つの非負多項式へ統合。
2. 五生成元u=6/7の第二行では、原稿の40/62より弱い44/68を使う。
   それでもtarget下界46/77で支払える。
3. antipodalの第一行は厳密な一般式`b1=h+4`を使わない。
   実P上界と調和評価で閉じ、h=4を別処理する。
   **厳密式b1=h+4の一般Lean exportは未証明**であり、原稿側で証明済みと記載してはいけない。
4. 幅5はq=3専用の実kernel/minorで閉じている。
   それを一般qのW_EDGEのrank公式とみなしてはいけない。

## 新規実行による検証

隔離cloneで、変更していない `scripts/verify_run18.py --fresh-test-cache` を実行した。
出力先は新設の
[`verification/run18/runs/independent_audit_20261115_r01`](../../verification/run18/runs/independent_audit_20261115_r01/verification.json)。
終了コード0、**183 commandの期待結果が一致**した。

* 新規Lex/Width production 37 moduleをすべて再ビルド。ログ上でも37個のBuiltを確認。
  buildは6040 jobs成功。
* project test cacheは空から作成し、**169 fixtureすべて終了コード0**。
  W_FIVE、W_SPARSE、dense資源の元の受入、Run15/16/17の回帰、
  標数0/2/3、最上端・消滅後、d=3・m=du+2・nonunit tの受入を含む。
* 未完四受入はそれぞれ指定宣言のunknown identifierだけで失敗。
  各ログが一行の当該errorだけであることも別に確認した。
* 15公開guard、実Leanの追加axiom拒否control、数値検算、隔離した旧checker replayも成功。
* **8,942宣言・新規701宣言**を実Lean環境から抽出。
  新規宣言の通常/explicit型を保存。raw出力を公開R05のraw出力と独立比較し、
  宣言名・型・公理依存を含む全recordが一致した。
  推移依存は`propext`・`Classical.choice`・`Quot.sound`のみ、自己依存なし。
* 新規実行開始前のverification/artifact **3,856件をbyte保持**。
  旧証跡や旧ZIPを更新して成功に見せていない。
* 記録されたcommand時間の合計は714.021秒。監査作業全体の所要時間ではない。

固定Leanは4.36.0-rc2、mathlibは`139105d28c7685a154cb3093f79edb2e16708099`。
既存baselineとmathlibのビルドcacheは再利用した。
**全baselineをcold rebuildしたとは主張せず、新規37 productionと全fixtureのcold確認である。**
元のworkspaceのcheckout/indexやproject cacheには書き込んでいない。
baselineのproject cacheは隔離cloneへコピーし、新規productionとtest cacheを空にした。
外部package cacheは既存固定版を共有参照した。

## 独立モデル・公開証跡

本番checkerをimportしない[独立モデル](check_core_models.py)を新規作成した。
4≤u≤10の全生成条件を満たす三内部offset集合と追加antipodal例、計208 profileを検査。
整数offsetのnBからQC基底と実変数作用の符号付きKoszul行列を構成し、
Q/F2/F3で別々に計624個のTor profileを計算した。反例なし。
antipodalでは実basis/P/Wとb1の指定値を有限範囲で照合した。

さらにd=1/3、m=du+2で416個のactual半群order計算を行った。
**この追加計算のsocleは次数2uまでの観測窓に限定**し、全socleの形式的計算とは表示しない。
非零socleを観測した窓28件、P_C≠P_Gの窓189件を含む。
有限検査・異標数の実験結果は、全称定理の代替にはしていない。
詳細は[モデル結果](core_models.json)。

[公開証跡の独立checker](check_published_evidence.py)で次を確認した。

* R05 source manifest 1,226件は現在のSHA256とproof/review/headのGit blob IDに一致。
  evidence 198件はSHA256・review/headのGit blob ID・directory coverageが一致。
* 公開summary、review決定、review本文のhash束縛も一致。
* Run18基準の全3,857追跡ファイルは、指定3ファイルの追記を除いて不変。
  指定3ファイルは元のprefixを完全保持。
* R05前にあったverification/artifact 3,653件もproof commitと同じbytes。
* 三つのRun18 ZIPすべてに、重複entryなし・全entry hash一致・CRC正常。
  最新ZIPは1,432 entry、SHA256
  `13b8f7b94c7e294558f9a6fc91c2782e9e34385b7c9f7cb6a8aa90c0ab03c271`。
  公開receiptとも一致する。

## 次の完成監査に残す注意

凍結`X_BHP_EK`は「与えられた同じHilbert関数のlex商への比較」とEK公式の契約である。
これだけで、Task 2の**一般Iに対するlex商の存在**が認証されたとは判断できない。
将来このIDを閉じる際は、lex存在・有限生成元の存在・実比較の構成も別途確認する必要がある。
今回はこのID自体がopenなので、PARTIALの誤認や閉鎖済み証明の欠陥には当たらない。

基準のRun16/17全数学、固定mathlib、公刊BHP/EK本文を独立にすべて再証明した監査ではない。
利用する入口の意味・新規接続・回帰・実公理依存を確認した。
未完四ID、一般antipodal b1等式、全NS-P14の完成は認証対象外。

監査中の最新workは`88dbd044ef7a8073d6d0bed6a7a4b550ed86a1bf`へ進んだが、
差分はRun19指令書の追加1ファイルだけで、Run18の数学sourceは同じだった。
Run19指令書自体は本監査の認証対象外。

監査ブランチは`audit/run18-20261115`。
追加するのは本監査ディレクトリと新しい独立検証runだけで、元のproof・status・ZIPは変更しない。
