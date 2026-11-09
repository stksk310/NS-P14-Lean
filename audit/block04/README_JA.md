# Block04 独立監査

2026年11月10日（JST）。判定：**rank 2・3の全5行の有限数値評価は合格。Block04に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`66e92970f9469a73db073dfc7da5b71800e5484e`、
`NSP14/Ordinary/LowRank.lean`。提出された証明・検証記録は変更していない。

## 検証結果

- Block04 manifestの52件すべてが一致。
- 同梱Block04 ZIPの53ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- ビルド・ソース再検査・Block04テスト・Block01〜03回帰・負のシフト検査・Block02仮定検査の8コマンドが終了コード0。
- 新規13定理は完全名を照合した。既存10・14・7件も含め、計44件の公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- 前三ブロックの証明ソース・テスト・固定環境はBlock03監査対象時点から変更されていない。
- 取り込まれたBlock02監査の16ファイルは、監査原本コミット `f5ef448` とバイト単位で一致。

固定環境はLean v4.36.0-rc2とmathlib `139105d28c7685a154cb3093f79edb2e16708099`。
ビルドは前ブロックの監査でソースから構築した同じ固定依存を再利用した。

## 重みと同じ資源列の確認

V02 §7 (7.3) の一般式と照合し、層0・1・`j+2` の区別、
tailの分母 `j+2+k` と `j+k`、rank 3第二行のhead係数 `8/3` は一致する。
非第一行の式の原稿上の範囲は `2≤k≤r`。今回の5行はその範囲内にある。

`Layers` は非負のhead・tailと任意の有限台を持ち、`tail_vanish` が全非零層を含むことを保証する。
mass・head上界・各行の評価は同じ `P` を参照し、別の列の評価を混ぜていない。
`Resources.toLayers` はhead・tail・台をそのまま保持する。
全rankの第一行とBlock03 scalarの一致も証明されている。

## rank 2

入力は `d≥0`、`mass≤dV`、`head≤2d`。
`V≤3` と `V≥3` の二つの評価は、境界 `V=3` で一致する。
結論は第一行が `d(V+1)` 以下、top行が `d(V−1)` 以下。
`d=0` を排除せず、三角数由来の下限やhead上界も加えていない。

追加Lean検査では `e=3,d=3,head=6,tail=0` が両方の最終評価を等号で満たすことを確認した。
この列は `Resources 2 3 3` の三角数head上界を満たせないことも証明した。
rank 2をより弱い `Layers` で扱う設計は、数値的に許される境界例を保持している。

## rank 3

入力は `e≥4,d≥6`、`mass≤dV`、`head≤3d`、`head≤e+d−7`。
第一・第二・top行は、それぞれ `d(V+1)`、`2d(V+1)`、`d(V−1)` 以下となり、V02 §9と一致する。

第一行で使う余裕の分子は、有理数全域で次の形に展開できる。

```text
d(V−1) − 4(e+d−7)
= 15 + 2(e−4) + (7/2)(d−6) + (d−6)(e−4) + (d−6)²/2
≥ 15.
```

追加Lean検査で恒等式と下界を証明した。紙上の第一行のtarget余裕はこの量の1/3であり、
`e=4,d=6` でも正になる。整数の丸めや有限サンプルに依存しない。

Block03からのadapterは三角数head上界を引き継ぐが、`head≤3d` は別の明示した入力として残る。

## 追加検査

[LowRankChecks.lean](LowRankChecks.lean) は警告なしでコンパイルした。
上記の余裕と境界例に加えて、rank 2の `head≤2d`、またはrank 3の `head≤e+d−7` を外すと、
残る条件を満たしても第一行がtargetを超える数値例を確認した。
これは数値入力についての反例であり、実際の半群の反例ではない。

独立した有理数実装では、紙上の一般重み式と簡約した5行を165箇所で照合し、
2,800件の有限資源最適化で中間評価と最終評価を確認した。
`d=0`、`V<3`・`V=3`・`V>3`、半整数を含むパラメータ、遠方のtailを含む。
この有限検査は補助検査であり、普遍証明はLeanの定理による。

## 合格範囲と残る接続

今回の「行」は有限資源の重み付き和であり、実際のKoszul/Tor rankではない。
actual towerから同じ列の総量・head上界を構成する部分、actual Torから(7.3)を得る部分、
actual targetの余裕(8.4)、Bettiへの移行は未実装。
rank 9以上のscalar閉鎖、actual sourceに対するO_LOW全体、M12・P14全体も今回の合格範囲に含まない。
提出側の範囲説明は、コードの仮定と一致する。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Ordinary/LowRank.lean
lake env lean tests/LowRank.lean
lake env lean tests/SmallScalar.lean
lake env lean tests/Sidon.lean
lake env lean tests/Resources.lean
lake env lean audit/DomainChecks.lean
lake env lean audit/block02/AssumptionChecks.lean
lake env lean audit/block04/LowRankChecks.lean
python3 audit/block04/check_low_rank.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[保存されたBlock02監査との一致](preserved_audit_check.json)／[独立した有理数検査](low_rank_rational_checks.json)

[ビルド](build.log)／[ソース再検査](source_recheck.log)／[Block04テスト](tests_and_axioms.log)／[Block01回帰](block01_regression.log)／[Block02回帰](block02_regression.log)／[Block03回帰](block03_regression.log)／[負のシフト検査](block01_domain_checks.log)／[Block02仮定検査](block02_assumption_checks.log)／[追加Lean検査](low_rank_checks.log)
