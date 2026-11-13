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
