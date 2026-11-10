# Block11 独立実装レビュー

2026年11月10日（JST）。別コンテキストのレビュー担当が12ソース、テスト、verifier、
範囲説明と対応台帳A18–A22をV02 §2 / V03 O_COORDと照合した。

判定：正しさ・完成範囲について指摘なし。

- NはA全体の乗算に対して閉じたactual ideal。任意の係数の和、dead積、headでない積も扱う。
- Qはactual ideal quotientであり、actual Apéry単項式を基底に持つ。
- AとQの各次数はactual G成分の像として定義し、その後に係数支持空間と同定している。
- 低次同型は自然な商写像。registered grading、Nの斉次性、Hilbert計数と最高次数も接続済み。
- 標準生成は最長表示のliveな原子分解を用い、任意の分解の積が生きるとは仮定しない。
- Artin性は体を仮定する。総k次元と一般のModule.lengthを説明上も区別する。

レビュー担当は `PATH=/tmp/ns-p14-lean/bin:$PATH lake env lean tests/AperyQuotient.lean` を独立実行しexit0を確認した。
旧42hash、120新宣言とreport名の一致、保存済み443公理依存報告も独立照合した。
全26コマンドは保存済み成功記録を確認しており、レビュー担当が全suiteを再実行したわけではない。
レビュー後に数学的ソースの修正はない。

追加のordinary半群m=e=3、δ=0、ν=1の境界例は実装担当が単体検証し、その後の全26コマンドも再実行して通過した。
この例は、m=1と異なりq₁が非零のまま高次区間が空になる境界を確認する。
新規120宣言＋旧323件の依存はpropext・Classical.choice・Quot.soundのみ。

未解決の指摘はない。完備化比較、同jump strataとjump≤ν、A・N・Tそれぞれの有限性、
S₀の表示、actual資源、Koszul/TorやP14全体の完成を認証するレビューではない。
