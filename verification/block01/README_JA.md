# Block 01：小rank scalarの数値部分

V03 O_SMALLのうち、同じ資源列からSO3の上界が得られた後の数値議論を形式化する。

- 三角数、volume、正の残余重みの有限和からSO3のupperを定義する。
- gapの二変数恒等式SO4を全有理数シフトについて証明する。
- 5行のg,A,bを定義式から正確に再計算する。
- 非負整数シフト `s,t : ℕ`、`4 ≤ r ≤ 8`、`r ≤ 5 ∨ s+t ≠ 0` の下でgapが正になることを証明する。
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

## 独立監査後の修正

正値性の定義域のコメントを明確化した。恒等式は全有理数シフト、正値性は上記の条件付き。
負の整数シフトの反例は `audit/DomainChecks.lean` に保存され、
`python3 scripts/verify_block01.py` で再検査される。
定義・定理の型・証明本体は監査提出版から変更していない。

このディレクトリのログ・manifestは修正後の現行ファイルを対象とする。
初回依存ビルドの `dependencies_build.log` は初回実行の記録として保持する。
初回の14項目manifestと検証結果は既存のBlock01 ZIPおよび `audit/` の照合記録に残す。
原稿SO3–SO5との対応は今回の独立監査の対象外であり、表記修正で検証済みになったとは扱わない。
