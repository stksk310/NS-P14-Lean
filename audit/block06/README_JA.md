# Block06 独立監査

2026年11月10日（JST）。判定：**全r≥9、有理数e≥10・δ≥a_rでのgap正値性と、資源を入力とするscalar評価は合格。Block06に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`14ebc6d0085f48541cbd96f6abc09728ecdfbcc0`、
`NSP14/Ordinary/LargeScalar.lean`。提出された証明・検証記録は変更していない。

## 検証結果

- Block06 manifestの61件すべてが一致。
- 同梱Block06 ZIPの62ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- ビルド・ソース再検査・Block06テスト・Block01〜05回帰・負のシフト検査・Block02仮定検査の10コマンドが終了コード0。
- 新規15定理は完全名を照合した。既存66件も含め、計81件の公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- 前五ブロックの証明ソース・テスト・固定環境はBlock05監査対象時点から変更されていない。

固定環境はLean v4.36.0-rc2とmathlib `139105d28c7685a154cb3093f79edb2e16708099`。
ビルドは前ブロックの監査でソースから構築した同じ固定依存を再利用した。

## 基点と差分の確認

V02 (S21)〜(S31)、V03 (O22)〜(O23)、台帳A06と照合した。
`baseSlope` は `G(11,a)−G(10,a)`、`baseStep` は `G(10,a+1)−G(10,a)` であり、
Block05と同じe=10・δ=aの基点に中心を置いている。
`SmallScalar.seed` のe=r+1との取り違えはない。

`g₀=(a+9)A+C`、`C<0` とBlock05の `g₀>0` から、Aの正値性を導いている。
δの最初の差分 `b=A+11−r−8α` も既存のgapから証明されている。
正値性を追加の仮定として受け取っていない。

cutoffはe・δを動かしても `D_r=largeCutoff r` のまま固定されている。
移動したδからcutoffを再計算する処理は含まれない。

## 偶奇比較と有理数への延長

`stepLower−floorStep` の恒等式の分子は
`(2D−a−1)(r−1)(a²+17a+144)`。分母は正で、床の下限 `2D≥a+1` から非負になる。
これにより、原稿のF₀・F₁の分岐を一つの比較へ置き換えている。
追加Lean検査でも、奇数三角数のrank 9で等号、偶数三角数のrank 11で狭義となることを確認した。

r≥9の `a≥4r` から、`floorStep>5/4`、従って `baseStep>5/4` が得られる。
β=1−α、s=e−10、t=δ−aとすると、二変数恒等式は

```text
G(10+s,a+t) = g₀ + sA + t(b−β/2) + β(t²/2+st).
```

`0<β<1` と `b>5/4` から `b−β/2>3/4`。
この下界を追加Lean検査で全rankについて確認した。
残る二次項はs,t≥0で非負となり、有理数の `0<t<1` も含めて正値性が成立する。
実際、元の `t(t−1)/2` はt=1/2で−1/8となるが、実装はこれを非負として扱っていない。

従って、台帳A06の偶奇分岐の統合と有理数への強化は有効である。
局所変更の最終原稿への反映と、最終的なLean・原稿の全体照合は残る。

## 同じ資源列からのscalar評価

`Resources.scalar_lt_large` は、同じRのhead・tail・総量・各上界からBlock03のSO3を導き、
今回のgap正値性と合成して `R.scalar<δ(V+1)` を得る。
`F≤upper` を仮定として戻していない。
有限台はcutoff以下に制限されず、全非零層を含む。

独立した有理数検査では、r=9〜128、シフト0・1/100・1/2・1・7/3・100について、
4,320組のgapと4,320件の有限資源最適化を確認した。
資源の総量と各上界は同じ列に課し、cutoffを越える層も含めて評価した。
cutoffを自由に指定した600件の比較恒等式も一致する。
また、多変数の正確な係数演算により、補正・差分・二変数展開・床比較に関わる5恒等式を照合した。
有限検査は補助検査であり、全域の根拠はLeanの普遍証明である。

## 合格範囲と残る接続

Block05の基点から、任意の有理数e≥10・δ≥a_rへの延長と、Block03の数値資源との合成は今回完成した。
一般のr≥4の全重み付き行をscalarが支配する評価は、まだ含まれていない。
actual tower・cutからの共通資源の構成、actualパラメータ、Tor上界、target余裕、Betti移行も未実装。
actual対象へのO_LARGE全接続、M12・P14全体は今回の合格範囲に含まない。
提出側の範囲説明は、コードの仮定と一致する。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Ordinary/LargeScalar.lean
lake env lean tests/LargeScalar.lean
lake env lean tests/SmallScalar.lean
lake env lean tests/Sidon.lean
lake env lean tests/Resources.lean
lake env lean tests/LowRank.lean
lake env lean tests/LargeSeed.lean
lake env lean audit/DomainChecks.lean
lake env lean audit/block02/AssumptionChecks.lean
lake env lean audit/block06/LargeScalarChecks.lean
python3 audit/block06/check_large_scalar.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[独立した係数・有理数検査](large_scalar_rational_checks.json)

[ビルド](build.log)／[ソース再検査](source_recheck.log)／[Block06テスト](tests_and_axioms.log)／[Block01回帰](block01_regression.log)／[Block02回帰](block02_regression.log)／[Block03回帰](block03_regression.log)／[Block04回帰](block04_regression.log)／[Block05回帰](block05_regression.log)／[負のシフト検査](block01_domain_checks.log)／[Block02仮定検査](block02_assumption_checks.log)／[追加Lean検査](large_scalar_checks.log)
