# Run19 独立レビューの記録方法

数学実装者の自己点検と最終独立レビューを分ける。ソース固定・fresh全検証後、許可された新しいwhole-branch reviewerへ、数学、10凍結型、V06経路、型/公理全被覆、verifier/adapter/negative controls/packagerの全体を渡す。

実レビュー本文と判定JSONはverification/run19/review/へ新規保存する。JSONはproof commit、実際に読んだevidence commit、検証summary/manifest、本文SHA256、10 ID、未処理指摘を束縛する。本文そのものを監査ZIPへ入れる。未処理指摘があれば公開gateを通さない。

このファイル自体をレビュー合格の証明にしない。確定した判定・Git bytes・公開結果はimmutable review receiptおよびcompletion receiptで確認する。
