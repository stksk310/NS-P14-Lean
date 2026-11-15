# Run19 V06指令の入力範囲と設計判断

2026-11-15 JST。ユーザーの依頼は、V06を軸に、先行する微調整を実行スレへ任せたうえでRun19のプロンプトを前もって作ること。

## 取得・確認した入力

- 最新origin/work: `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。明示fetchで確認。
- Run18: 六ID COMPLETE、最終R16の280 checks／268 fixtures、10662宣言、新規2421宣言。proof source `a5f480c5136042597fceae23ad06d2ef3923ed02`。実装・検証・レビュー・公開の記録を読む。
- [ユーザー添付の原文](2026-11-15-v06-alignment-order-input.txt)は21582 bytes、SHA256 `51372b807584acf3cd78d0b022a44658e4bfcdb6ae51db41aaeb43a448dfe66c`。操作上の依頼は今回のユーザーメッセージを正本とし、添付に含まれる実装指令は先行同期の仕様資料として扱う。
- 添付の五項目はEndpointの全j・停止非依存、antipodal/non-antipodal第一行の整数slack、共通第二行から高次行、denseのt=2/t≥3二枝。N4の新cubic/actual接続、Run19、全P14新合成は明示的に対象外。
- V06候補ZIPの共有hashは`788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d`。ZIP実物・V06本文は本指令作成時点で未提供。ローカルとorigin/workに`proof_sharp_v6/`はなく、GitHubのv06名branch検索も空。hash一致やN4本文の読了は主張しない。
- 旧[Run19指令](../plans/2026-11-15-run19-n4-small-closure-order.md)とV03依存表の10 ID、N4置換稿、V02幅4証明、実Endpoint/TwoRows/TwoMonomial/InternalSocleBasis、三点成長・SC、target/正規化APIを確認した。

## 採用した構成

先行V06同期をRun19へ混ぜる案、旧Run19をそのまま使う案、同期後baseからV06主経路のRun19を始める案を検討し、最後を採用する。ユーザーが微調整を別実行に予定しており、旧Run19はRun18の現在の完成状態・最新検証・V06経路に追従していないため。

新指令は旧ファイルを上書きせず、[V06版Run19指令](../plans/2026-11-15-run19-v06-n4-small-closure-order.md)として追加する。既存数学source・旧証跡・既存指令のbytesは保持する。これは計画文書の改訂であり、V06同期またはRun19の実証明ではない。

Run19の担当10 IDと最終actual出口を保ち、V06で変わった中間経路は原稿から再固定する。添付にないcubicの式や適用下限は推測しない。取得が必要な正確な入力として、指令のTask 1に原稿receiptと命題対応表を置いた。原稿未取得の部分は確定していないが、独立な原典調査・小生成元の準備は進められる。

## 検証・公開の判断

V06は旧BASE以前のEndpointも変更する。旧Run18 verifierのbyte不変ガードを弱める案は採用しない。先行同期の新しい変更管理・検証を継承し、Run19自身のbase／許可リスト・全実質command対応・fresh範囲・改変旧宣言coverage・経路検査を新snapshotへ束縛する。

旧R16の280 commandは出力先や監査probeが旧ディレクトリを指すため、文字列の直接replayを指示しない。先行同期で増えたfixture・guard・依存検査も含めて、新しい排他的出力先へ写像する。

指令書だけの変更についてLean数学のcold回帰は再実行しない。文書の参照・添付hash・既存source不変・ID被覆・旧未完記載の持込み・V06入力未取得の表示を点検して通常Pushする。
