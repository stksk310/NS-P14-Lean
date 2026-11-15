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
