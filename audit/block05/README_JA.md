# Block05 独立監査

2026年11月10日（JST）。判定：**全rank r≥9の基点gap正値性は合格。Block05に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`542b19ec5ce3f4728ccd314b3598ce09d0b51cb6`、
`NSP14/Ordinary/LargeSeed.lean`。提出された証明・検証記録は変更していない。

## 検証結果

- Block05 manifestの57件すべてが一致。
- 同梱Block05 ZIPの58ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- ビルド・ソース再検査・Block05テスト・Block01〜04回帰・負のシフト検査・Block02仮定検査の9コマンドが終了コード0。
- 新規22定理は完全名を照合した。既存44件も含め、計66件の公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- 前四ブロックの証明ソース・テスト・固定環境はBlock04監査対象時点から変更されていない。

固定環境はLean v4.36.0-rc2とmathlib `139105d28c7685a154cb3093f79edb2e16708099`。
ビルドは前ブロックの監査でソースから構築した同じ固定依存を再利用した。

## 証明の確認

`triangularNat` の自然数除算は整数三角数に一致し、有理数の `triangular` との等式も証明されている。
`largeCutoff` は `D_r=⌊a_r/2⌋+1` を自然数で計算する。
床の両側評価、Dの単調性、増分の上界は偶奇を落とさず処理している。

`harmonic n` は1からnまでの調和和であり、tailへの変換は3からnまでの和を正確に取り出す。
`seed_eq_threshold` は、既存の `gap` をそのまま用い、
`G_r(10,a_r)=(r−1)(a_r+9)(T_r−H_D)` を証明する。別の近似gapへの置換はない。

`harmonic_lt_barrier` はr=10の基点と `Nat.le_induction` による帰納で全r≥10を証明している。
閾値との比較から基点gapを正にし、r=9は直接の有理数計算で補う。
有限個のrankから無限範囲へ外挿していない。

## 原稿からの置換と台帳A05

参照はV02 §11、V03 O_LARGE、および `docs/LEAN_PAPER_ALIGNMENT_JA.md` A05。
置換証明は有効であり、定義と結論は対応している。

調和和の各増分項を最初の項で抑え、床の評価から

```text
H(D_(r+1)) − H(D_r) ≤ (r+2)/(a_r+3) < B(r+1) − B(r)
```

を得る。右の比較の分子はx=r−10の正係数四次式で、r≥10で正。
`B<T₁≤T_r` の分子の分解と分母の正値性も一致する。
独立した係数演算でも、この二つの多項式恒等式を照合した。

追加の[LargeSeedChecks.lean](LargeSeedChecks.lean) で、次の境界を確認した。

- 全自然数rで `2D_r=a_r+2−(a_r mod 2)` が成立する。
- r=9では `B(10)−B(9)−11/48=−7/240` であり、新しい増分比較をそのままr=9から始められない。
- r=9では `T₁(9)−B(9)=−1/72` でもある。今回の障壁による連鎖にはr=9の直接計算が必要。
- r=10では粗い増分上界が `2/r` を `1/145` 上回る。この粗い評価から原稿の中間評価 `<2/r` を導くことはできず、実装どおり障壁と直接比較する必要がある。

従って、台帳が「原稿の鋭い中間評価自体は主張しない」と説明するのは正確である。
この局所置換を最終原稿へ反映する作業と、最終的なLean・原稿の全体照合は残る。

## 独立した有理数検査

正確な係数演算で二つの多項式恒等式を照合したほか、以下を確認した。

- r=0〜10000の10,001件について、床・偶奇・cutoff増分の条件。
- r=9〜128の120件について、既存定義から直接計算した基点gapの正値性と閾値恒等式。
- r=10〜128の119件について、調和和・障壁・閾値の連鎖。
- cutoffを自由に指定した30件の基点恒等式。

基点の正確な値 `B(10)−H₂₈=1833472237/80313433200`、
`G₉(10,45)=5845533/7436429` も一致した。
rankの有限検査は補助検査であり、普遍証明はLeanの帰納による。

## 合格範囲と残る接続

合格範囲は `G_r(10,a_r)>0` という無限の基点列。
e=10は有理式の評価座標であり、r>9でe=10のactual sourceの存在を主張していない。
`SmallScalar.seed` の評価点はe=r+1なので、後続の差分評価ではこの基点座標を区別する必要がある。

e方向の係数とδ方向の差分の正値性、任意のe≥10・δ≥a_rへの延長、
大rankでのBlock03資源評価との合成は未完。
actual tower・資源上界・Tor上界・target余裕・Betti移行、O_LARGE全体、M12・P14全体も今回の合格範囲に含まない。
提出側の範囲説明は、コードの仮定と一致する。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Ordinary/LargeSeed.lean
lake env lean tests/LargeSeed.lean
lake env lean tests/SmallScalar.lean
lake env lean tests/Sidon.lean
lake env lean tests/Resources.lean
lake env lean tests/LowRank.lean
lake env lean audit/DomainChecks.lean
lake env lean audit/block02/AssumptionChecks.lean
lake env lean audit/block05/LargeSeedChecks.lean
python3 audit/block05/check_large_seed.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[独立した係数・有理数検査](large_seed_rational_checks.json)

[ビルド](build.log)／[ソース再検査](source_recheck.log)／[Block05テスト](tests_and_axioms.log)／[Block01回帰](block01_regression.log)／[Block02回帰](block02_regression.log)／[Block03回帰](block03_regression.log)／[Block04回帰](block04_regression.log)／[負のシフト検査](block01_domain_checks.log)／[Block02仮定検査](block02_assumption_checks.log)／[追加Lean検査](large_seed_checks.log)
