# Block02：Sidon差単射・数値Apéry・scalar接続

2026年11月9日（JST）。ソースはNSP14/Combinatorics/Sidon.lean。

## 完成した範囲

1. 任意の可換加法群の有限Sidon集合について、相異なる点の順序付き差が単射になる。
2. 正整数mの巡回群で、e点のSidon集合は e(e−1)≤m−1 を満たす。素数・奇数を仮定しない。
3. 加法部分モノイドS⊆ℕの実際の剰余最小元の一意性を証明した。
4. 数値Apéry-pairデータから剰余集合を構成し、濃度eとSidon性、m≥e(e−1)+1を証明した。
5. m=e+δ、e≥1のとき、上記データから δ≥(e−1)²を導いた。
6. このSidon証拠からrank6–8の悪い角を排除し、Block01へ接続した。
   境界版ではr≥6かつs=0の場合にだけ証拠を要求し、内側では不要にした。

`small_gap_pos_of_apery_pairs` は数値Apéryデータからgapの正値性へ接続する。
`scalar_lt_of_boundary_sidon` はSidonの境界証拠とSO3の上界からscalar不等式を返す。

## 入力として残した数値データ

AperyPairDataの全フィールドは明示した局所仮定であり、新しいaxiomではない。

- value：e個の相異なる自然数。
- value_min：各valueがSのその剰余の最小元。
- pair_min：すべての二項和もSのその剰余の最小元。
- pair_unique：数値的に等しい二項和の添字は順序の交換を除いて同じ。

Sは実際のAddSubmonoid ℕだが、このデータだけから最小生成系や埋込次元を定義したとはしない。
ここでeはデータの点数であり、実際の半群の埋込次元と一致させるのは後続の構成である。

**未完の橋：actual tangent coneのQ=A/NとそのQ₂を構成し、最大二次層から
0と非m原子が上記のデータを持つことを証明する。**
今回はこの存在を証明したことにせず、入口として残す。SO3資源上界・Tor/Bettiも後続工程である。
したがってO_SIDON全体、M10全体、P14全体が完成したという扱いはしない。

## 検証

```sh
python3 scripts/verify_block02.py
```

このクラウドでの固定版は以下で実行した。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block02.py
```

lake build、新ソースの再検査、テストと14個のaxiom report、Block01の回帰テストを実行する。
依存はpropext・Classical.choice・Quot.soundの標準論理基盤のみ。

テストはZMod7の鋭い例、ZMod8の合成数例、ZMod2の反例、
3つの悪い角の全Sidon集合に対する不可能性、内側で証拠を要求しない接続を含む。
有限例は普遍定理の代わりではない。普遍定理はソース中の単射・濃度・不等式の証明による。

Block01のSmallScalar.leanは変更せず、rootのNSP14.leanを新モジュールの公開importで拡張した。
