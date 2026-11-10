# Block07 独立監査

2026年11月10日（JST）。判定：**共通資源と明示した境界証拠を入力とする、全cut rank・全行の数値閉鎖は合格。Block07に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`51c558e1fe7b264edab204d389e7f2e6226e3096`。
`Scalarization.lean`、`TargetMargin.lean`、`NumericalClosure.lean` を照合した。
提出された証明・検証記録は変更していない。

## 検証結果

- Block07 manifestの70件すべてが一致。
- 同梱Block07 ZIPの71ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- ビルド、3ソースの再検査、統合テスト、Block01〜06回帰、既存の2監査検査の13コマンドが終了コード0。
- 新規25定理は完全名を照合した。既存81件も含め、計106件の公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- 前六ブロックの証明ソース・テスト・固定環境はBlock06監査対象時点から変更されていない。

固定環境はLean v4.36.0-rc2とmathlib `139105d28c7685a154cb3093f79edb2e16708099`。
ビルドは前ブロックの監査でソースから構築した同じ固定依存を再利用した。

## 全行scalar化

V02 (7.3)、(10.1)と台帳A07に一致する。
正規化係数は `choose(r−1,k−1)`。head、tail、層0の係数をそれぞれ評価し、
同じ非負の層とδに掛けて有限和を取る。
`1≤k≤r` を保ち、top行も含む。

`k=2` のtail比較の分子は `(r−3)(j+2)−2` であり、r≥4で非負になる。
r=4・j=0は等号。k≥3では分母比較の両分子の非負性を確認している。

rank 3をこの一般scalar化へ含めることはできない。
追加Lean検査で、head=0、tailの最初の層を205とした有効な `Data 3 200 6` を構成した。
第二行は627/2、係数2倍の第一行は892/3となり、一般scalar化は破れる。
同じDataに対する `all_rows` は、rank 3の直接評価によって正しく成立する。

## 明示式からのtarget余裕

R_kとL_kはV02 (8.2)、(7.2)直前の式と一致する。
e−r+k、e−1の係数は有理数で減算し、自然数の切り捨て減算を混入させていない。
形式上e<rも扱う補助定理の検査では、e=δ=0・r=4・k=1でR=L=−6となることも確認した。
これは形式的な二項式の検査であり、負のBetti数を主張する例ではない。

`R_k(0)=L_k` と
`R_k(δ+1)−R_k(δ)=(e+δ) choose(δ+r−1,k−1)` は正しい。
δについて帰納し、二項係数の単調性から必要な余裕(8.4)を得ている。
台帳A08の置換証明は有効で、target余裕を資源フィールドとして仮定していない。
元のVandermonde余剰Γ_kの全恒等式まで証明したという扱いもしない。

追加Lean検査では第一行の余裕が全自然数e,δとr≥1に対して
`R₁−L₁=δ(V+1)` と厳密に一致することを証明した。
また、有効な `Data 2 3 3` で最終比較そのものが等号になることを確認した。
統合定理の非狭義不等号は、この数値入力の範囲で必要である。

## rankの統合とSidon条件

rank 2、rank 3、4〜8、9以上の分岐は全範囲を覆う。
rank 2に三角数条件を課しておらず、δ=0を含む。
小rankの自然数シフトは `r+1≤e`、`a_r≤δ` を使って切り捨てのない差として構成している。
`toResources` は元のhead・tail・台を保持し、全評価は同じ `Data.layers` に適用される。

`Boundary` は6≤r≤8かつe=r+1のときにだけ要求される。
この条件を資源条件だけから取り除くことはできない。
追加Lean検査では、有効な `Data 6 7 21` としてhead=6、tailの添字0〜10を各27、
添字11を12とした有限列を構成した。総量・各上界はすべて満たすが、

```text
L₁ + weighted_row₁ − R₁ = 831/8008 > 0
```

となる。一方、法28で7点のSidon集合は存在せず、`Boundary 6 7 21` は偽である。
これはBoundaryを外した数値緩和の反例であり、現在の定理の仮定は満たさない。
actual半群やP14の反例とは扱わない。
実装はこの条件を保持し、Apéry-pair版も同じ境界で証拠を要求している。

## 独立した有理数検査

正確な整数・有理数演算で、18,270件の重み比較、84,260件のtarget式・差分・余裕を照合した。
形式的なk>rや負の係数も含めて検査した。
共通資源の上限を満たす303組のパラメータで、全3,297行の最終比較を確認した。
rank 2のδ=0、全rank分岐、top行、法1000・2000・5000の非自明な境界Sidon集合を含む。
Boundaryを外した数値反例はrank 6・7・8の3件で確認した。
有限検査は補助検査であり、全域の根拠はLeanの普遍証明である。

## 合格範囲と残る接続

`Data.all_rows` のr,e,δは自然数である。明示した共通資源条件とBoundaryから、
全r≥2・1≤k≤rで `L_k+weighted_row_k≤R_k` を証明する。
数値targetの余裕も今回証明されている。

残るのはactual towerから全資源条件を同時に構成する部分、最大actual Q₂からのApéryデータ構成、
actual Koszul/Tor上界、明示target式とactual ordinary target Betti容量の同定、最終Betti移行である。
`relative_rows` は将来のTor上界を明示した仮定として受け取り、それ自体でactual Torを構成していない。
他の幅枝、P14全体、最終原稿との全体照合も今回の合格範囲に含まない。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Ordinary/Scalarization.lean
lake env lean NSP14/Ordinary/TargetMargin.lean
lake env lean NSP14/Ordinary/NumericalClosure.lean
lake env lean tests/OrdinaryNumerical.lean
lake env lean tests/SmallScalar.lean
lake env lean tests/Sidon.lean
lake env lean tests/Resources.lean
lake env lean tests/LowRank.lean
lake env lean tests/LargeSeed.lean
lake env lean tests/LargeScalar.lean
lake env lean audit/DomainChecks.lean
lake env lean audit/block02/AssumptionChecks.lean
lake env lean audit/block07/NumericalChecks.lean
python3 audit/block07/check_numerical_closure.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[独立した有理数検査](numerical_rational_checks.json)

[ビルド](build.log)／[scalar化ソース](scalarization_recheck.log)／[target余裕ソース](target_margin_recheck.log)／[統合ソース](closure_recheck.log)／[統合テスト](tests_and_axioms.log)／[追加Lean検査](numerical_checks.log)
