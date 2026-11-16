# Run17後の20run計画再校正

20は担当を整理する運用目標であり、証明完成の定義を緩める上限ではない。
Run17ではX_KNESERとX_SCの元の一般命題を、actual consumerまで同じrunで閉じる。

今回のproductionは28 Leanファイル、2,886行。
うちKneserの二ファイル954行は、出典・license・原ソースhashを保持した
Bakšys–Dillies実証明の再利用である。依存更新や外部oleanへの依存ではない。
SCは位置付き部分列の新規主鎖を実装した。finite regressionの約0.2秒は開発工数と別物。
baseline build記録は2026-11-13 07:55 UTC、数学接続後のcold検証着手は08:50台UTC。
この間隔は原典調査・実装・compile/debugを含み、純粋な証明CPU時間ではない。
採用したcold回帰時間・宣言数・source数はclosure statusの`verification.evidence`が指すJSONを正本とする。

Run16の「Kneser/SCは約1〜3倍」という暫定幅より今回が小さくなった主因は、
一般Kneserの再利用可能な形式証明を発見したことと、SCのsharp一意性を短く直接証明できたこと。
この短縮率をBHP/EK/LTVへそのまま適用しない。

| Run | 実際に受け取る入力と担当 | 再校正した完了条件・不確定要因 |
|---|---|---|
| 18 | 同じDのW有限尾和・ceil成長・四点例外、Run16全行Tor評価。BHP/EK、疎幅多項式、幅側target支払い | 公刊入力の実証明を先に調べる。Run17の外部証明発見による短縮は保証できない。必要なら長runを延長する |
| 19 | q=2のW≤1+u²/4、実QC零和自由性、SC unit/二ラベル関係、Run16四行R/Rhat | socle三角形、R<c₀、混合語の長さと最終計数、N4/LTVをactual側から閉じる。unitをsourceの変換と誤認しない |
| 20 | ordinary Run15、endpoint Run16、群/列 Run17、残り幅/N4出口 | 全域分岐・境界・元の完備半群環のactual Bettiへ合成。最終凍結命題、全回帰、原稿との一致を独立に監査 |

残り三番号は保持するが、BHP/EK/LTVの不足を未証明の入力へ戻して三runに収めない。
Run18着手時には、予定名より実exportの型と公刊証明の依存量で順序と工数を更新する。
Run17だけでP14全体のLean証明が完成したという表示はしない。

最初の合格cold実測: 159コマンド、154 fixture、8,241宣言うち新規406。
コマンド実測合計 506.05秒。
新規production/testの空cache、過去原本3260ファイルのbytes照合を含む。

公開tooling修正後の採用cold: 160コマンド、154 fixture、宣言数は同じ。
コマンド実測450.127秒、Run01–16原本3,260件と既存Run17証跡368件を保持。
数学sourceは最初の合格snapshot dc66f3aから変更なし。
