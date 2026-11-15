# Run19 V06指令の入力範囲と設計判断

2026-11-15 JST。ユーザーの依頼は、V06を軸に、先行する微調整を実行スレへ任せたうえでRun19のプロンプトを前もって作ること。

## 公開資料の到着後：現在の入力状態

ユーザー共有commit `a7504eea25f02728d1be6cd0082e8484d639dbe2` を明示fetchし、初稿を含む `3cf5e15` からfast-forwardした。V06本文とZIPは取得済みになった。以下の初稿時の未取得記録は履歴であり、現在の障害ではない。

- [N4確定契約と照合結果](2026-11-15-run19-v06-n4-checked-contracts.md)に、公開三資料のhashとN1b→N4a→N4b/c→actual targetの接続を記録した。
- 新cubicはu=6+zで `12*(2*C(u,3)−(5u²/4−2u+4))=4z³+45z²+140z+36>0`。第2行の`+V`補正を用いず、第3・4行はUの二差とTの二項係数比で払う。初稿Task 3の未確定部分をこの経路へ具体化した。
- 小幅u=5の上界(24,13,2)／target最小(25,25,9)、u=4の(12,5,0)／(12,7,1)、u=3のd=1一致／d≥2のV≥6支払いを指令へ固定した。five/sparseの共通higher wrapperをN4へ強制しない。
- 実ZIP SHAは共有候補と一致。51 payload・CRCと公開manifest136ファイルを再照合した。算術checkerは書込みを行わない`--math-only`でexit0、22 symbolic identities、366959 finite transcription checks、6660 partition sanity casesを確認した。個別のV05/V06補助検査数は生JSONに保持し、単純合算して独立ケース数を作らない。
- 原稿公開差分にLean・tests・audit・scripts・固定依存の変更はない。先行五項目のLean経路同期・検証完了は、この資料公開からは認定しない。Run19の開始条件としてその証跡確認を維持する。

## 初稿作成時に取得・確認した入力（履歴）

- 最新origin/work: `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。明示fetchで確認。
- Run18: 六ID COMPLETE、最終R16の280 checks／268 fixtures、10662宣言、新規2421宣言。proof source `a5f480c5136042597fceae23ad06d2ef3923ed02`。実装・検証・レビュー・公開の記録を読む。
- [ユーザー添付の原文](2026-11-15-v06-alignment-order-input.txt)は21582 bytes、SHA256 `51372b807584acf3cd78d0b022a44658e4bfcdb6ae51db41aaeb43a448dfe66c`。操作上の依頼は今回のユーザーメッセージを正本とし、添付に含まれる実装指令は先行同期の仕様資料として扱う。
- 添付の五項目はEndpointの全j・停止非依存、antipodal/non-antipodal第一行の整数slack、共通第二行から高次行、denseのt=2/t≥3二枝。N4の新cubic/actual接続、Run19、全P14新合成は明示的に対象外。
- V06候補ZIPの共有hashは`788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d`。ZIP実物・V06本文は本指令作成時点で未提供。ローカルとorigin/workに`proof_sharp_v6/`はなく、GitHubのv06名branch検索も空。hash一致やN4本文の読了は主張しない。
- 旧[Run19指令](../plans/2026-11-15-run19-n4-small-closure-order.md)とV03依存表の10 ID、N4置換稿、V02幅4証明、実Endpoint/TwoRows/TwoMonomial/InternalSocleBasis、三点成長・SC、target/正規化APIを確認した。

## 採用した構成

先行V06同期をRun19へ混ぜる案、旧Run19をそのまま使う案、同期後baseからV06主経路のRun19を始める案を検討し、最後を採用する。ユーザーが微調整を別実行に予定しており、旧Run19はRun18の現在の完成状態・最新検証・V06経路に追従していないため。

新指令は旧ファイルを上書きせず、[V06版Run19指令](../plans/2026-11-15-run19-v06-n4-small-closure-order.md)として追加する。既存数学source・旧証跡・既存指令のbytesは保持する。これは計画文書の改訂であり、V06同期またはRun19の実証明ではない。

Run19の担当10 IDと最終actual出口を保つ。初稿では本文未取得を明記して式を代作しなかった。公開後は、取得済みV06の正確なcubic・適用下限・小幅・actual接続をTask 3へ固定し、Task 1を原稿の再照合と受入型の凍結へ更新した。

## 検証・公開の判断

V06は旧BASE以前のEndpointも変更する。旧Run18 verifierのbyte不変ガードを弱める案は採用しない。先行同期の新しい変更管理・検証を継承し、Run19自身のbase／許可リスト・全実質command対応・fresh範囲・改変旧宣言coverage・経路検査を新snapshotへ束縛する。

旧R16の280 commandは出力先や監査probeが旧ディレクトリを指すため、文字列の直接replayを指示しない。先行同期で増えたfixture・guard・依存検査も含めて、新しい排他的出力先へ写像する。

本更新も指令・照合文書と新しい検算記録に限り、Lean数学のcold回帰は再実行しない。文書参照・原稿／ZIP／添付hash・既存source不変・10 ID被覆・新cubic転記・小幅・旧未取得表示の更新を点検して通常Pushする。これはRun19の実装やLean完成監査ではない。
