# Block07：ordinary数値評価の全域・全行統合

2026年11月10日（JST）。ユーザーの操作頻度を減らすため、三つの証明単位と接続・検証をまとめた。

1. [Scalarization.lean](../../NSP14/Ordinary/Scalarization.lean)：全行を第一行scalarで支配。
2. [TargetMargin.lean](../../NSP14/Ordinary/TargetMargin.lean)：具体的target容量から余裕を証明。
3. [NumericalClosure.lean](../../NSP14/Ordinary/NumericalClosure.lean)：全cut rank・全行を一本に統合。

Block01–06のソース・テスト・固定環境を保持する。

## 今回の到達点

`NumericalClosure.Data.all_rows` は同じ有限資源の条件と境界Sidon証拠から

∀k, 1≤k≤r → L_k+Σ_t W_k(t)H_t≤R_k

を返す。r=2、r=3、4≤r≤8、r≥9の全範囲を覆い、top行も含む。
`all_rows_of_apery_pairs` は境界証拠をBlock02の数値Apéry-pairデータから供給する。

これはordinary側の数値部分の統合であり、actual接錐から全資源を構成したという意味ではない。
実際のTor rank c_kやtarget Betti公式は、引き続き後続の意味の接続である。

## 同時に供給する入力

`Data r e d` のr,e,dは自然数で、dはmultiplicity deficitとして使う数値。

- 同じ `Layers`：H₁、H_{j+2}、有限台、台外ゼロ、非負性。
- 2≤r、r+1≤e。
- S=d+H₁+ΣH_{j+2}≤dV、H₁≤rd、H_{j+2}≤e+d−1。
- r≥3のときだけa_r≤d、H₁≤e+d−1−a_r。

rank2には三角数条件を課さず、d=0の空塔を許す。
`Boundary r e d` は6≤r≤8かつe=r+1のときだけ、法e+dでe点の強いSidon集合を要求する。
その数え上げが三つの悪い角を排除する。内部点や他のrankで証拠を要求しない。
Apéry版の局所データも、mが実際のmultiplicity、eが埋込次元であることまでは含意しない。

## 全行scalar化

隣接二項係数の関係k choose(r−1,k)=(r−k) choose(r−1,k−1)から重みを正規化する。
headの重みはC(r+1)/(k+1)、tailは原稿の分数和となる。
k≥3は分母比較、k=2は差の恒等式、layer0は非負の二項係数関係で抑える。
同じ非負のhead・tail・dに項別に掛け、有限和を取って `row_le_scalar` を得る。
証明はr≥4、1≤k≤rで普遍的であり、有限表の確認ではない。

## target余裕の短縮

`target` は原稿(8.2)のR_k、`lower` はL_kの明示式。
e−r+kなどの係数は有理数の減算であり、自然数の切り捨て減算ではない。
実際の適用範囲ではe≥r+1なので原稿の非負係数と一致する。

`target_zero` がR_k(0)=L_k、`target_step` が

R_k(d+1)−R_k(d)=(e+d) choose(d+r−1,k−1)

を証明する。二項係数の単調性からd方向に帰納し、
d(V+1) choose(r−1,k−1)≤R_k−L_kを得る。
元の長いVandermonde展開を仮定せず、target余裕を資源フィールドとして要求もしない。
原稿へ移せる証明は対応台帳A08に保存した。

## 統合とactual接続の境界

rank2/3の直接評価、small scalar、large scalarを同じ `Data.layers` に適用する。
小rankでは自然数のe・dからシフトを構成し、三角数castと角条件を接続する。
大rankではBlock06の有理数評価に自然数パラメータを渡す。
最後に `target_margin` を適用して具体的なR_kまで進む。

`Data.relative_rows` は将来のc_k≤L_k+ΣWHを明示した入力として受け取る。
この入口だけでactual Tor評価を証明したとは扱わない。
未完はactual towerと全資源条件の同時構成、最大Q₂からのApéryデータ、
actual Koszul/Tor上界、ordinary target Betti公式と最終Betti移行、他の幅枝・P14全体。

## 検証と再現

```sh
python3 scripts/verify_block07.py
```

このクラウドでは先頭に `PATH=/tmp/ns-p14-lean/bin:$PATH` を付ける。
build、3ソースの再検査、統合テスト、Block01–06回帰、既存2監査検査を行う。
新規25件と既存81件の公理依存を検査し、標準3公理以外を拒否する。
新規定理は完全名を照合し、既存6ブロックのソース・テスト・固定依存もhash照合する。

テストにはrank2のd=0、r=4,k=2の鋭いtail、top行、
任意のr≥3と任意に遠いtailを持つ非空の内部profileを含む。
非自明な境界例として法1000、7点0,1,3,9,27,81,243の数値Apéry-pairデータを作り、
Data 6 7 993の全行比較へ実際に渡す。
S=ℕ全体の数値データであり、この例の法1000をS固有のmultiplicityとは主張しない。
三つの悪い角でBoundaryが存在しないことも検査する。
原稿対応は [変更台帳A07–A09](../../docs/LEAN_PAPER_ALIGNMENT_JA.md) を参照。

過去のmanifest・ZIP・検証ログは履歴として保持する。
今回の照合対象はこのディレクトリのmanifest。
`interface_before.log` と `target_interface_before.log` は実装前の不在確認で、成功記録とは区別する。
