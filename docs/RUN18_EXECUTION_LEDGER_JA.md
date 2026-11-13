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
