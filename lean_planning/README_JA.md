# P14 Lean化計画 R01

[全体図と計画書](P14_LEAN_FORMALIZATION_PLAN_JA.md) を入口にする。

- [全18モジュールの範囲・前提・追加工数・受入条件](P14_LEAN_MODULE_CATALOGUE_JA.md)
- [mathlibの公開ソース調査](P14_LEAN_LIBRARY_AUDIT.md)
- [全体図PNG](P14_LEAN_OVERVIEW.png)／[SVG](P14_LEAN_OVERVIEW.svg)
- [計画の独立レビュー](audits/PLAN_REVIEW.md)

modules.jsonは全50項目の割当・依存・工数、mathlib_inventory.jsonは公開ソース根拠を記録する。
1人日は熟練者＋AIの約6時間の実働であり、AI単独の実行時間ではない。
工数は初回試作前の判断で、納期の保証ではない。
最初の10–20人日の校正試作で、既存宣言の適用・実際の証明速度・不足APIを測る。

計画の構造・費用・参照は次で検査できる。

~~~sh
python3 -B lean_planning/checks/check_plan.py
~~~

このスクリプトはLeanを呼ばず、証明の真偽や期間の正確さを検証しない。
Lean実装・toolchainインストール・コンパイルは今回行っていない。
work/は計画作成時の独立した調査・見積の記録であり、採用した総数と方針は主計画書に従う。
