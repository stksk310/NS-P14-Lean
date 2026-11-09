# Block 01：小rank scalarの数値部分

V03 O_SMALLのうち、同じ資源列からSO3の上界が得られた後の数値議論を形式化する。

- 三角数、volume、正の残余重みの有限和からSO3のupperを定義する。
- gapの二変数恒等式SO4を全有理数シフトについて証明する。
- 5行のg,A,bを定義式から正確に再計算する。
- 整数s,t≥0の全域でgapが正になることを証明する。
- rank6–8の角の除外条件は明示した仮定。将来actual Apéry–Sidonから供給する。
- scalar_lt_of_upperはSO3を受け取って目標のstrict inequalityを返す。

実際の半群・接錐・資源列、SO3そのもの、Apéry–Sidon、Bettiへの移行はこのブロックに含まない。
P14全体やM12全体が完成したという意味ではない。

標準のelanが利用できる環境では、rootで次を実行する。

```sh
lake build
lake env lean tests/SmallScalar.lean
```

このクラウド環境ではreleases.lean-lang.orgとcache.mathlib.orgへの通信が拒否される。
Lean公式GitHub releaseから同じ固定版を取得し、mathlibはキャッシュを使わずソースビルドする。
実行コマンドと実際の検証結果はログとverification.jsonに保存する。
