# Run17 初回独立レビューと修正対象

fresh-context `/root/run17_final_review`、範囲584f92d8..dc66f3a。
数学28ファイル、6受入、指令全文、公開型、source/evidence hash、
過去3,260ファイルと全公理依存を独立確認。全6受入と追加契約を/tmpで再elaboration。
数学的欠陥なし。

公開前判定はNot Ready。Critical 0、Important 3、Minor 1。

1. verifierと数値helperが既存Run17証跡を上書きする。新規のexclusive出力先へ統一する。
2. packagerが既存ZIP/checksumを上書きする。既存先を拒否し、temporaryで検証後にexclusive公開する。
3. PASS reviewが実snapshotへ束縛されていない。実在commit、source/evidence manifest、
   各fileのGit bytesを照合し、publication-only変更だけを明示的に許す。
4. paper ledgerのSC exportが「予定」とされている。証明済みの現在形へ直す。

これは修正前の履歴。最終判定は同じreview seatによる再確認と
`RUN17_CLOSURE_STATUS.json`を参照。
原本の数学sourceに修正要求はなく、公開処理と文面を直して全検証を再実行する。
