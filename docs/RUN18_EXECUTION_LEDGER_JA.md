# Run18 実行台帳（PARTIAL）

指令: `131f559a9ad495891f0aab487f969bf91b5a447f`。開始baseline: `c4fd8153f55bb231aab4168a47c1546888fa7ab0`。実装は独立worktree `/workspace/NS-P14-Lean-run18` の `run18/implementation-20261113`。既存監査worktreeを保持した。

## 実装と受入

- Task 1：最新workとremote監査branchを確認。六IDの元の受入を定義し、hashを固定。公刊本文の直接取得はCONNECT 403で失敗し、取得できたと記載していない。
- Task 2：一般の斉次商に対する次数piece有限性、実graded/total Torの接続を実装。BHP/Pardue・lex存在・EK本体は未構成。凍結した受入は該当公開宣言の不在だけを理由に失敗する。
- Task 3/4/6/7：未完。原稿の元の量化と担当を保持し、失敗する受入を明示。
- Task 5：実距離和→余りつき体積→第一行全e分岐→第二行→正規化容量の全高次行→元のactual source/targetを実装。凍結W_SPARSEの閉鎖証明がコンパイルした。
- 先に存在しない公開宣言を要求する受入を実行し、失敗ログをscratchへ保存した。失敗にはcache未構築の試行もあり、それを正しいREDに数えず、依存構築後にunknown declarationの失敗を取り直した。
- baseline full buildは5964 jobs成功。最初の実装milestoneは5982 jobs成功。focused buildを各証明後に実行し、失敗した型class/減算/商の正規化を修正した。
- `tests/WidthSparse.lean` はe=6..10、最小疎幅、d=1とd=3、Qと標数2/3、最上端・消滅後を含む。元のR>0かつP_C≠P_Gの例 `(m,d,a,u)=(12,1,{1,2,8,9},10)` では、実基底からP_C=15、P_G=10、R=1もLeanで確認した。

## 判断の記録

1. Ruling: 実行はinlineで維持。cloud skillのhelper scriptはexecutorに配置されていないため、同等の明示ledger、base SHA、失敗/成功ログを手動で管理した。誤っていれば作業状態の復元性が落ちるため、この公開台帳とcommitで追跡可能にした。
2. Ruling: BHP/EK本体が未構成でも独立なTask 5を実装した。六IDの契約は弱めず、閉じた一IDだけを最終台帳へ記載する。誤っていれば公刊入力の達成度を過大表示するため、五IDの未完受入とPARTIAL表示を残した。
3. Ruling: 第二行のe=7/e≥8の紙上分岐を、e=7+vの非負多項式に統合した。元の範囲・実Tor接続は保持。符号や範囲を誤れば全高次行が壊れるため、Leanの恒等式と別Python計数で検証する。
4. Ruling: Run18全体の終了条件は満たしていない。BHP/EKの新規一般定理を構成できておらず、残る幅分岐も未完のため、COMPLETE/全域NS-P14を宣言しない。PARTIALとして証跡を保存し、継続すべき正確な型を保持する。

新規productionのcold build、空のtest cacheでの全既存fixture、公理依存・通常/explicit型、旧証跡のbyte保持、独立計数と公開guardは `verification/run18/runs/` の各排他的な検証ディレクトリへ保存する。途中の失敗を含む再実行では既存ディレクトリを上書きしない。

## cold検証の失敗と修正

最初のcold検証r01は旧154 fixtureとRequested/PartialClosedGoalsを通過したが、最後のWidthSparse具体例processがSIGKILL(-9)で停止した。cgroupの上限16 GiB、peakが上限付近、累積OOM kill counter=4を観測した。counterは累積値であり当該processだけの発生回数とは表示しない。r01を失敗として保存し、成功記録へ上書きしない。

Ruling: 計算を含むLean fixtureを `-j1 -M12288` で直列elaborationし、processごとのメモリ上限を12 GiBにする。数学source・43の受入命題・通常のdecideによる核検査は維持する。誤っていれば検証が遅くなる/明示的に失敗するが、失敗を成功に変換しない。SOURCE_SHAとsnapshotを検証開始時に保存し、以後の失敗も構造化JSONへ残す。

進行中に公開された指令監査 `2f0baa1703ec514a5b757264f70c19d7f6227856` も確認した。指令の必須修正0件。これは今回の実装の合格認証ではなく、BHP/EKの一般証明が大きな未完義務である点を再確認したもの。

単独のraw fixtureは1 threadでもR=1のdecideで再帰深さ8192に達し失敗した（最大RSS 10,315,468 KiB）。通常の36 Betti比較だけのprobeは約6秒で成功したため、問題を具体例の再帰的offset和評価に局所化した。

Ruling: 当該具体例では四重和から全intervalになることを帰納で証明し、全次数で元のoffsetSumsと一致する検算専用表を作った。computedMinima/order/survivors/socleWindowとの一致もLeanで証明して置換する。元の43命題は削除・弱化しない。誤った表なら等式のLean証明が失敗するため、未検証の数値入力として扱わない。

初期focused shellの複数commandの最終exitだけではWidthSparse単独の成功を認定できなかったため、それを成功根拠から外した。修正版は個別subprocess終了コード0、64.745秒、最大RSS 2,727,840 KiBで全43命題を通過した。新規cold全回帰でさらに再確認する。数学production sourceと凍結契約は変更していない。

## 公開theorem interfaceの判定修正

r02では全159 fixture、5つの未完受入、数値検算・公開guard・旧検算replay・Lean環境抽出が通過したが、verifierがConstantInfo.axiomInfoを一律拒否したため最終判定が失敗した。8,429宣言の実際の推移公理依存に違反は0件で、6,258件はLeanの公開theorem interfaceが返す形だった。元のweight_head_leはbaselineにも証明本体がある。

Ruling: import後のConstantInfoの見かけだけで追加公理と断定せず、collectAxiomsの実依存と自己依存で判定する。実際の追加公理は自身の名前を依存に含むため拒否する。既存の証明済みexported stubの受入と、隔離された本物の追加axiomの拒否をLeanの対照実験で確認した。対照用axiomはverification内の専用processだけで宣言し、production・fixture・本環境監査から一切importしない。誤判定なら禁止公理を通す危険があるため、このnegative controlを全検証へ組み込む。

r01/r02はいずれも失敗として保持し、最終の新規cold検証をr03へ保存する。公開guardはcold検証、全check通過、証跡coverage、review済み追加payloadも要求する。

## 最終cold検証 r03

`fa3787cff6e924690ea7abc1bc522fb43a06be02` をsource snapshotとして、新規production lib/irとtest cacheを空にして再構築し、全159 fixtureを通過。未完5契約は指定宣言の不在だけを理由に失敗することを確認した。全172検証commandの期待結果が一致し、全8429宣言・新規188宣言の公理依存/型を抽出した。実推移依存は許容3公理のみで、3165の既存証跡をbyte保持した。

この成功はW_SPARSE一IDを持つPARTIAL snapshotの検証であり、Run18全体の完成ではない。別視点の最終review・bundle・通常Pushの結果は最終review記録と公開receiptに記載する。未完の計画workspaceは継続用に保持する。

## 2026-11-14 継続

最新work/実装branchはaa29347で一致し、新着のRun18監査修正はなかった。既存worktreeと未完workspaceを継続使用した。

Ruling: BHP/EKが未構成の間も、それに依存しないdense実資源、AP edge、五生成元の小幅/高次/非antipodalを先に構成する。六IDを弱めず、dense資源のconjunctと幅の部分分岐を全ID閉鎖と混同しない。誤っていれば完成度を過大表示するため、五つの失敗受入とPARTIALを維持する。

Ruling: 五生成元u=6,7の高次行では既存のactual rank envelopeがtargetの下界を払えるので、原稿の追加Euler改善を前提にしない。第二行上界44/68とtarget46/77を直接証明する。u=7のR>0改善には実高次QC基底によるh2≤P−5を用いる。誤っていれば数値の接続が壊れるため、同じ元のRとactual TorをLeanで追跡する。

Ruling: 五生成元u≥8の高次行は全構造を先に閉じ、antipodalの第一行/実presentationを未完として分離する。非antipodal第一行の基点をu=8..11に拡げ、u≥12は一つの非負多項式で払う。原稿より弱い中間上界でも同じactual結論を証明しており、未証明のpresentationを入力しない。誤っていればantipodalを閉じたと誤読されるため、export名・型と台帳で範囲を明示する。

新規受入moduleを先に実行した不在RED、各Lean構成途中の失敗、focused結果を `verification/run18/continuation_20261114/` に保存した。不在REDは新moduleの不存在であり、凍結五契約のunknown-declaration受入とは別のもの。型class上限と有理数/Natの明示変換、依存するZMod型へのgeneralizeを避ける修正を行った。旧原本は書き換えない。

R04 cold検証：source `f1732ce45500a191df2b76780f5feddd3d87adfa`、全179 command・165 fixture成功。全8594宣言、新規353宣言の通常/explicit型と実公理依存を抽出し、許容三公理のみ。既存証跡3388ファイルをbyte保持。元の五IDの指定宣言不在も確認した。旧audit branch一覧を再確認し、Run17独立監査の新着branchはなく、Run18の指令監査のみだった。

## 2026-11-14 第2継続：五生成元の全幅

開始時の最新workはe4bb337で実装branchと一致し、新着監査修正branchはなかった。元のworktreeで継続した。

Ruling: antipodalの実QC基底・presentation・次数・変数作用・Tor対応・P/Wを構成する。第一行は未証明の厳密b1式を入力せず、証明済みのP上界と調和評価から同じactual比較を払う。誤っていれば原稿の厳密式まで閉じたと誤読されるため、b1=h+4の一般式は未証明と明記し、比較の別経路と分ける。

Ruling: W_FIVEのu=5は一般W_EDGEの完成を待たず、四つのactual offset集合を分類して独立に閉じる。内部2ケースの実核5生成元と元のKoszul微分の符号付き単位minor、端2ケースの次数2基底一意性を用いる。反射によるG/R同一視は行わない。誤っていれば標数2や元の向きでrankが変わるため、符号±1のみのminorをLeanで証明し、標数0/2/3を独立検算する。

全数学moduleのbuild（6038 jobs）と凍結W_FIVE consumer、actual presentation/Tor/P/W、幅4/5/6/7/8/9・nonunit t・d=3,m=du+2の全行fixtureをfocused検証した。各subprocessの終了コードはfocused02.jsonへ記録。失敗したelaboration試行と修正ログもantipodal_20261114へ保存し、過去の成功証跡を上書きしない。最新closed IDはW_SPARSE,W_FIVEの2件。BHP/EK、一般一欠落、dense lex閉鎖、全域合成の4件は開いたまま。

公開guardは2件閉鎖を要求し、W_CLOSEまで閉じたという過大表示を拒否する新しいnegative controlを追加した。全新規source/fixture/verifier/checker/ログを新source snapshotへ束縛し、新しいR05 cold検証・独立最終review・PARTIAL ZIP・通常Pushを行う。

R05 cold検証成功：source `bc554ffc0231c0e83fdf4c62673e438cc123c417`、全183 command・169 fixture、8942宣言・新規701宣言の通常/explicit型・実公理依存を確認。許容三公理のみ。source manifest 1226 entry、evidence manifest 198 entry、3653既存証跡をbyte保持。未完4契約は指定宣言の不在だけを理由に失敗し、W_FIVEの元の受入は成功した。

Final: Ruling: reviewerが認証対象外とした一般b1=h+4、未完4ID、公刊本文の未取得部分は証明済みと表示しない。実比較の別経路とコンパイル済み凍結契約のみを閉鎖根拠とする。誤っていれば完成度を過大表示するため、正確な未完型を次節へ残す。将来のZIP/remoteは別途実測し、静的reviewの合格をPush成功の代用にしない。

## Run18 継続用引継ぎ（五生成元閉鎖後、PARTIAL）

凍結された六IDのうちW_SPARSEとW_FIVEは証明済み。Run18全体の完了条件はまだ満たさない。契約本文は `audit/run18/RequestedGoals.lean` をそのまま保持する。

| ID | 現在の実export・未完境界 |
|---|---|
| W_SPARSE | `NSP14.Run18.sparse_closed`。元のS、任意体、e≥6、u≥2e−2、全i。 |
| W_FIVE | `NSP14.Run18.five_closed`。元のS、任意体、e=5、物理狭幅、全u・全i。 |
| X_BHP_EK | `NSP14.Lex.bhp_ek : Requested.X_BHP_EK` は不在。一般の斉次商の任意標数graded比較、全Hilbert関数lex、実EK解消が必要。 |
| W_EDGE | `NSP14.Run18.edge_closed : Requested.W_EDGE` は不在。u=q+1の実AP比較は完成。q=3,u=5もW_FIVE経由で完成。q≥4,u=q+2の実作用/rankとtarget補正が必要。 |
| W_DENSE | `NSP14.Run18.dense_closed : Requested.W_DENSE` は不在。`dense_resources_closed : Requested.DenseResources` は完成。DenseClosureは一つの実lex商とK調和計数/容量支払いが未完。 |
| W_CLOSE | `NSP14.Run18.width_closed : Requested.W_CLOSE` は不在。e=5と疎幅は完成。一般一欠落とdenseを閉じて元のSへ全域合成する必要がある。 |

次の独立した証明作業として、一般一欠落の実Koszul作用を元のQC基底上で表し、符号付き単位minorまたは像の明示基底からrankを証明する。今回の幅5のminorはq=3専用であり、一般qへのrank公式として流用しない。denseはBHP/EKの完成後に実lex consumerへ進む。既存の末尾4本の未完受入は追加仮定を入れずに閉じる。

antipodalで新しく使える実exportは `antipodalPresentation`、`antipodalModuleIso`、`antipodal_actual_betti`、`antipodal_coreP`、`antipodal_wordVolume`。必要なcoprimeはgcd(t,h)=1でありgcd(t,2h)=1ではない。一般の厳密b1=h+4は未証明で、W_FIVEの第一行は実P上界による別経路を使う。有限検算のb1値を一般定理の入力にしない。

残るBHP/Pardue/EKは固定mathlibに該当証明を確認できておらず、新規の大きな形式化を要する。公刊本文の取得制限と調査範囲は `RUN18_INPUT_INVENTORY_JA.md` に記録。残りを必ず2runで終えられるとは評価しない。Run19/20へ進む前にRun18の正確な閉鎖条件を維持する。

## 2026-11-15：ユーザー指示によるRun18再開

Run18未完のままRun19指令を渡した判断は訂正した。最新work88dbd04をRun18 branchへfast-forwardで保持し、Run19は着手保留。残るRun18全契約の完成が現在の目的であり、今回の内部checkpointをRun18完了としない。

Ruling: 一欠落幅は実二次blockの完全rank等式を先に作る代わりに、元のKoszul微分で構成した符号付き単位minorの下界と、実chain dimension/Eulerから十分な全行評価を導く。凍結W_EDGEの元の型を変更しない。誤っていれば原稿の厳密式も証明済みと誤認されるため、厳密式は独立有限検算のみに留め、一般Lean exportは実下界と比較とする。

W_EDGEの元の凍結受入がGREEN。q3..9の12 actual sourceでQ/標数2/3の全行比較、d3,m=du+2、両端/内部の欠落をfocused検証。実推移公理依存はedge_closed/actual_boundary_rank/lex raiseで許容三公理のみ。独立checkerは22 actual coreと10290整数補正検査を通過。root6062jobs成功。各失敗・成功ログを新しいedge_20261115/lex_20261115へ保存。

Ruling: 新規productionがHomologicalへ追加されたため、cold verifierはLex/Width directoryだけでなく、それ以外の新規productionのlib/IR各fileも退避して再構築する。誤っていれば既存oleanをcoldと誤表示するため、退避対象をfresh_cache.jsonに記録し、全source/evidenceをgit bytesへ束縛する。

残る障害は一般の任意標数BHP/Pardue/EKと、それを使うdense閉鎖・全域合成。固定mathlib/既存sourceに必要な一般比較は確認できていない。arXivの指定原典PDF/HTMLもこの環境でCONNECT403となった。未取得の本文や未構成の解消/圧縮を供給済みとはしない。読める原典URLの有無をユーザーへ非同期で照会し、独立な証明/検証を継続する。

R06 cold検証成功：source `62c30ae798871d4eb55703df29e2897a770d29b9`、全188 command・174 fixture、9203宣言・新規962宣言。許容三公理のみ、3901既存証跡をbyte保持。新規Homologicalもcold再構築。閉鎖W_SPARSE/W_FIVE/W_EDGE、未完X_BHP_EK/W_DENSE/W_CLOSE。これは内部checkpointであり、ユーザーのRun18完了要求を満たしたとは扱わない。

2026-11-15 EK証明継続：実colon等式、一般可換環の実短完全列、変数倍のactual Koszul homology零写像、lex一生成元追加のordinary Tor加法性を新規4 moduleで証明。3 consumerを個別exit0/警告0で確認し、次数1/2生成元を持つ実lex ideal (X0,X1²) の標数0/2/3例もGREEN。root6070jobs成功。4主要exportの実公理依存は許容三公理のみ。REDログは対象公開宣言の不在、失敗elaborationログも同じ新規directoryに保持。R06はこれらの追加前の内部snapshotで、新規4module全回帰は未実行。X_BHP_EKを閉じたと数えず、graded colon計算/有限生成元帰納/BHP比較/lex存在/dense/globalを引き続き実装する。
新着独立監査47aeeb4を読み、208 manifest entryのhashを照合してmerge84d7655で保持。修正必須0件、認証対象は以前の58a0f54の二閉鎖のみ。今回R06のfresh reviewerは三閉鎖のみを承認、9203宣言・全source/evidence/旧bytes束縛を確認（report verification/run18/edge_review_20261115.md）。どちらもRun18全体を認証していない。

2026-11-15 ordinary EK milestone：NSP14.Lex.IsLex.ordinary_ek はproperな実lex ideal、任意体、実極小生成元の任意有限集合g、全i≥1について商のordinary β_i=Σ_g C(max(v)−1,i−1)を証明。実predecessor idealと有限生成元順、実colon短完全列、実変数null-homotopy、実座標商の全行C(r,i)計算を接続。座標商は補変数の各正則作用を証明してactual Koszul homology同型で除去し、finite k-chainを非Artin商に仮定しない。empty/all coordinate idealsと全homological rowsも同じ定理に含む。
focused03：8 named consumer fixtureと公理probeの9 command個別exit0/警告0、root build成功。実lex ideal(X0,X1²)の極小生成元集合を証明し、実ordinary行(2,1,0)をQ/F2/F3で適用。主要ordinary EK exportの推移公理は許容三公理のみ。追加後のcold全回帰はまだで、R06は以前の62c30ae sourceに対する内部記録として保持。既存verification/artifactに変更なし、凍結契約hash不変。
元のRequested.EKは内部次数deg(v)+i−1まで要求するため、このordinary公式をEK/六IDの閉鎖と数えない。次は実graded map/完全列と内部次数を接続。BHP/Pardue・lex存在・dense/globalも未完。R06をRun18完了とせず継続する。
通常atomic Push dd36b20をwork/実装branch両方で実測し、両remote SHA一致・clean checkoutを確認済み。以後のordinary EK追加はこの公開後の継続であり、公開済み証跡の書換えではない。

2026-11-15 graded infrastructure：DirectSumSplit/GradedKoszulSplit/GradedKoszulMap/GradedKoszulExactを構成。actual degree inclusionのchain retractionと交差零を構成、actual内部homology単射、実斉次Koszul mapとdegree projection自然性を証明。各degreeの完全列はtotalの実前像を自然射影して構成（有限chainを仮定せず）。全体のactual left homology mapが零という実入力から、全internal degreeで実Betti加法性を証明。これは一般のgraded SES補題であり、比較結論付き証明書でBHP/EKを置換したものではない。
3 named fixture＋公理/公開型probeの4 command個別exit0/警告0、root build成功。主要5exportは許容三公理のみ。公開型にhf/hg/hS/hzが正しく残ることを#checkで確認。最初のred1件は≫のopen不足だったためREDに数えず、open修正後のunknown-name REDを保持した。暗黙のcoefficientFunctor.obj展開でrwが失敗する箇所はcongrArgとtransで実等式を接続し、前提を追加していない。公開済みverification/artifactは無変更。
ordinary EK source ae7da74はwork/実装branchへ通常atomicPush済み、両remote実測SHA一致・cleanを確認。最新追加4moduleはfocused検証済みだがR06 cold snapshotには含まれない。六IDは引き続き3閉鎖/3未完。
次の具体的証明：artinGradingのactual homogeneous monomial像/quotient maps、actual shifted gradingとdegree補正、coordinate quotientのgraded集中（ordinary C(r,i)は完成）、graded EK有限生成元帰納。一般BHP/Pardue/lex存在の形式証明は依然未構成。ユーザー依頼は全Run18完了であり、内部milestoneを完了/Run19移行に変えず継続。

2026-11-15 graded EK：`NSP14.Run18.ek_closed : Requested.EK` が元の凍結契約そのものを証明。properな実lex ideal、任意体、全i≥1・全j∈Int、実極小生成元集合に対して、商の内部次数deg(v)+i−1と寄与C(max(v)−1,i−1)を保持する。実斉次像/商map、実grading shift、実colon SESの次数付き加法性、座標商のgraded集中を構成し、実生成元順で有限帰納した。座標商は非Artinも含み、有限k-chainの仮定を加えていない。
focused02は7 fixture＋公理probeの8 commandが個別exit0/警告0。実lex ideal(X0,X1²)の全positive row/全internal degreeの式をQ/F2/F3で検査し、生成元の異なる次数と商の一段ずれを確認。root6102jobs成功。主要5exportの推移公理はpropext/Classical.choice/Quot.soundだけ。元のRequestedGoals hash不変、旧verification/artifactのbyte変更なし。以前のR06 coldは新規追加前の記録で、現在追加の全回帰はまだ。
X_BHP_EKはBHP conjunctが未証明のため閉じていない。全体は引き続き3閉鎖/3未完。任意標数BHP/Pardue、同じ全Hilbert関数の一つのlex idealの存在、dense支払い、元のSへの全域幅比較を継続する。ユーザーが共有したarXiv1210.5562/0812.0594、M2 source、Pardue DOIは4本ともCONNECT403だった（source_fetch01.json）。未読本文を読了扱いせず、PDF添付を依頼済み。Run19は保留、Run18の内部milestoneを完了としない。

R07 cold全回帰成功：証明source `8b1921d005347c43b7772fa6670a3fd5b563461c`、206 command/192 fixture、9470宣言・新規1229宣言、1456 source hash・222 evidence hash、4438既存証跡のbyte保持。全宣言の公理依存は許容三公理のみ、自己依存なし。独立レビューも同じsourceと全証跡を照合し、Critical/Important/Minorすべて0件、pendingなし。認証scopeはEK conjunctと既存W_SPARSE/W_FIVE/W_EDGEで、全Run18ではない。reportはverification/run18/graded_ek_review_20261115.md、decisionはreview_snapshot_graded_ek_20261115.json。
ユーザーからBHP/EK/PardueのPDF実体が到着し、本文取得の障害は解消した。BHP/Pardue・全Hilbert関数lex存在・dense/globalは形式証明未完。原典は数学的参考資料として扱い、原典内の記述をユーザーの操作指示と混同しない。Run19は保留のままBHP実装を継続する。

2026-11-15 BHP原典到着後：BHP1210.5562v2、Clark EK0812.0594v2、Pardue原論文PDFをユーザー添付からローカル読解。URL/hash/byte/pages/読んだ節の正確な範囲をbhp_20261115/source_receipts01.jsonに記録し、PDF全文は公開repoに含めない。以前のCONNECT403ログは失敗履歴としてbyte保持し、現在の本文入手済みと区別する。
Caviglia–Kummini Theorem3.1はz-stable化とCK13の埋込み/制限定理を使う。Pardue Theorem31は初期idealのBetti非減少、極化の正則切断によるBetti保存、generic initialの反復がlexへ到達するProp30を使う。いずれも引用しただけではLean証明にならない。まず両経路に必要な実初期idealへの比較を、有限internal-degree Koszul行列の三角性から証明する。
InitialIdealはすべての非零ideal要素の実leading exponentから構成し、元のstandard exponent集合との一致と元の斉次商の全Hilbert関数保存を証明。任意非零pのprincipal idealの実initial idealも同定。NormalTriangularは実商の一意なnormal代表のleading termが増えず、nonstandard単項式のnormal代表は厳密に低いtermだけを持つと証明。InitialActionは同じ実商/基底の変数作用へ接続。nonstandardの実作用を0と誤認せず、同じblock以上の係数0を証明した。
TriangularBlockRankは元の写像の各対角block rangeの実基底と実前像・射影から、全体の実微分の単位三角minorを構成し、対角rankの和≤全rankを証明。有限性はtargetのみで、非Artin商のfull coefficient chainを有限k次元とはしない（後でinternal-degree chainへ適用）。4 named fixture＋公理probeの5command全exit0/警告0、root6110jobs成功。主要6exportの推移公理は許容三公理のみ。
これらは初期idealへのactual graded Betti比較そのものには未接続で、BHP/EK全体の閉鎖ではない。最後のcold R07は8b1921d sourceのEKまでを認証し、この4moduleは含まない。追加後cold全回帰は未実行。次はactual graded chain基底/augmented exponent blockと実initial quotientのblock一致を構成し、三角rankから全β_{i,j}(I)≤β_{i,j}(in(I))を閉じる。BHP/Pardueのlexへの変形・全Hilbert lex存在・dense/globalも未完、Run19は保留で継続する。

BHP graded chain接続の継続：KoszulSlotGradingは元のrecursive chain基底のhomogeneityを証明し、そのreprが実slot射影後の元の係数座標と一致、基底値が実slot inclusionと一致することを証明。HomogeneousBasisPiecesは斉次基底を実degree pieceへ制限し、その次数のlabelだけの有限性からfinite pieceと実dimensionを導く。GradedKoszulBasisは実internal-degree chainの基底と元のwhole-chain座標の一致を証明。商全体のArtin/finite-k chainは仮定しない。
TriangularBlockRankを拡張し、literal sum Σ P_a d Q_aのrank≤actual dのrankを証明。Q_aの像は対応source block内、P_a dの三角性は実写像の入力として保持し、後で元の標準単項式作用から放電する。各対角rangeの実基底/実前像/延長された座標で単位三角minorを作り、rank和下界とrank(sum)上界を接続した。未証明の初期ideal比較を入力してはいない。
focused03の4 fixture＋公理probeは個別exit0/警告0。主要4exportの推移公理は許容三公理のみ。root6116jobs成功。既存ログを変更せず新規build03..等へ失敗/修正/成功を保持。以前のR07は追加前の8b1921dの証明snapshotで、この追加のcold全回帰は未実行。閉鎖ID数は3のまま、EK conjunctのみ別途完成。次はactual graded quotient chainのaugmented exponentごとの射影を実構成し、initial quotientの微分がそのliteral diagonalであることを証明して実Betti比較へ接続する。BHP/Pardueのlexへの変形、lex存在、dense/globalも継続する。
EK/R07認証済みcheckpoint23e5146はwork/実装branch双方への通常atomic Push後に実remote一致・cleanを確認。以後のBHP準備追加はこの認証scope外であり、Run18全体は未完、Run19は保留。

2026-11-15 初期idealへの実graded Betti比較が完成：`NSP14.Lex.quotientGradedBetti_initial_le` は任意Field k、任意q、任意の実斉次ideal I、全i∈Nat・全t∈Intについて、β_{i,t}(T/I)≤β_{i,t}(T/in_degLex(I))を証明。Artin/proper/標数0/無限体の追加仮定はない。Iと実initial idealの全Hilbert関数一致も既に証明済み。
ArtinGradedChainは各実degree chainの有限性を実standard exponent labelから供給。InitialBoundaryは実dの各成分を元のsigned variable actionへ同定し、augmented exponent順で三角性、同じexponentでは実±1 incidence、実monomial quotientでは異exponent blockが0であることを証明。InitialTransportは同じ実exponent/slot集合のfield-linear基底同型で初期idealの実dをtransportする。これはchain map/homology同型の主張ではなく、各actual boundary rankを保存するfield-linear同型だけを使用する。
InitialDiagonalは元のactual dのliteral射影和Σ P_a d Q_aとtransportしたinitial dの等式を全基底成分で証明。有限label集合は元の実internal-degree source/target chain基底の像から構成する。BasisBlocksが係数の実三角性から射影/単位三角minorのrank補題を放電し、実initial boundary rank≤元のboundary rankを得る。最後に両actual complexesの有限chain homology rank恒等式と実chain dimension一致を使い、全graded β不等式へ接続。負internal degreeやi=0/上端も同じ全称定理に含む。原典名のaxiom、比較証明書、未証明resolutionを入力しない。
focused06は5 named fixture＋公理probeの6commandすべてexit0/警告0。実binomial ideal(X0²+X1²)について全行/全internal degreeのinitial比較をQ/F2/F3で適用。root6128jobs成功。主要4exportの推移公理は許容三公理のみ、公開型を保存。focused05はfixtureのhomogeneous span witnessでLean表現の接続に失敗した履歴として保持し、membership↔IsHomogeneousの正規lemma適用後をfresh focused06へ記録。旧証跡は更新しない。
これは一般BHPの最初の変形段階であり、lexまでの一般変形・停止と全Hilbert関数lex存在は未証明。W_DENSE/W_CLOSEも未完、六IDは3閉鎖/3未完のまま。以前のcold R07は8b1921dのEKまでを認証し、この13moduleの追加は含まない。次のcold R08で新規source/全fixture/全公理/旧bytesを検証し、その間も原典の次の変形段階を検討する。Run19は保留、Run18全体完了と誤表示せず継続。

R08 cold全回帰成功：証明source `ed7f5cda20f054142bc9d5eb04574707bda9d8a0`、218 command/204 fixture、9626宣言・新規1385宣言、1586 source hash・234 evidence hash、4768既存証跡のbyte保持。全宣言の推移公理は許容三公理のみ・自己依存なし。新規Lex/Endpoint/Homologicalの13moduleをcold再構築。独立レビュアーが全raw/processed宣言、normal/explicit型、source/Git bytes、全manifest、旧4768/前4438/baselineの保持を照合し、Critical/Important/Minorすべて0・pendingなし。report verification/run18/initial_betti_review_20261115.md、decision review_snapshot_initial_betti_20261115.json。
認証対象は実initial idealへの全graded Betti比較と以前のEK/三幅ID。一般のmonomial-to-lex変形と停止、全Hilbert lex存在、dense/globalは認証していない。Run18全体は未完、Run19保留。次のdistraction試作は/tmpのみでR08/review対象外。原典PDFの入手障害は解消済みで、未完理由を本文未入手と誤表示しない。

2026-11-15 distraction線形同型の構成：DistractionMonomialは実積D(a)とD(a+e_i)=L_i(a_i)D(a)、斉次性、変数特殊化を証明。GenericDistractionは独立係数の実線形形式と各次数の実係数行列を定義し、対角特殊化で恒等行列になることから両行列式の非零を任意非自明可換環で証明。GenericDistractionFieldは実係数環のFractionRingへ移し、任意Field kで両行列の実可逆線形写像を構成。DistractionLinearEquivは各実斉次多項式pieceの基底でこれを接続し、DirectSumから多項式環全体の実field-linear同型を構成。全単項式の像が定義どおりのD(a)であり、homogeneityを両方向で保つことを証明。ring同型・chain同型・Betti保存はまだ主張していない。
focused07の2 fixture＋公理probe、focused08の4 fixture＋公理probeは全command個別exit0/警告0。主要exportの推移公理は許容三公理のみ。root_build09は6174 jobs成功。失敗したmapMatrix表現・pieceのcoercionのelaborationも新規logに保持。凍結契約・既存証跡を変更しない。R08/reviewは以前のed7f5cdだけを認証し、今回4moduleのcold全回帰は未実行。六IDは3閉鎖/3未完、EK conjunctのみ別途完成。次は実monomial idealの像のideal性・全Hilbert関数保存・actual Koszul比較を構成し、lexへの反復と停止、dense/globalを継続する。Run19は保留。
5cd8aa6577c8a2da429d027e144d2fb90e7f86dbはwork/実装branch両方への通常atomic Push後、remote SHA一致とclean checkoutを実測済み。

DistractionIdeal/DistractionHilbert追加：任意k・qの実generic coefficient field上で、全D(a)のk-linear spanが実idealとなることを証明。各変数を実可逆係数行列の逆像から線形形式の一次結合へ表し、D(a+e_i)の積恒等式で変数倍の閉性を放電。多項式帰納で任意の乗法閉性へ拡張した。元の実monomial ideal Iに対し、像へのmembership iff元の線形同型の逆像がIに属する、actual ideal span一致、実斉次性、actual quotientのfield-linear同型を証明。
DistractionHilbertはquotient同型と逆写像が元のstandard-monomial gradingの各実degreeSpaceを保つと証明し、各Int次数の実piece同型を構成。`genericDistraction_sameHilbert`で全Nat次数の元のquotientHilbert一致を証明。ring-linear/chain同型とは主張しない。元idealはgeneric coefficient field上のもの；任意の基礎体idealのscalar extension/descent、Betti保存、lex停止は別途未完。
focused09の2 fixture＋公理probeは個別exit0/警告0。主要6exportの推移公理は許容三公理のみ、公開型を保存。root_build10は6178 jobs成功。Hilbert RED01はgradedAlgebra instance不足も含むため正しいREDとは数えず、instance追加後にmissing宣言だけで失敗するRED02を保存。既存証跡・凍結契約は不変。六新規distraction moduleのcold全回帰と独立レビューを次に行う。六IDは3閉鎖/3未完、Run18を継続、Run19保留。
