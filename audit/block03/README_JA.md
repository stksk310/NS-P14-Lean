# Block03 独立監査

2026年11月10日（JST）。判定：**数値資源を入力とするSO3と小rank SO5への接続は合格。Block03に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`ff69aecb56433881f72f926883ab1701a732d5cd`、
`NSP14/Ordinary/Resources.lean`。提出された証明・検証記録は変更していない。

## 検証結果

- Block03 manifestの30件すべてが一致。
- 同梱Block03 ZIPの31ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- Lean v4.36.0-rc2と指定mathlibで、ビルド・ソース再検査・Block03テスト・Block01回帰・Block02回帰・負のシフト検査の6コマンドが終了コード0。
- Block03の7定理は完全名を照合した。前二ブロックの10件・14件も含め、公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- Block02監査時点からの前二ブロックの差分は、Block01のシフト範囲を説明するコメントの修正だけ。定理文・証明、Sidonソース、両テスト、固定環境に変更はない。

ビルドは前二ブロックの監査でソースから構築した同じ固定依存を再利用した。

## 紙上SO3との対応

参照は `auditability_search/ORDINARY_PAPER_REDUCTION_JA.md` §2 (SO3)、§3 (SO5)。

`R.head=H₁`、`R.tail j=H_{j+2}`、`d=δ=H₀` であり、tailの分母は `j+3`。
この `d` はordinary側のmultiplicity deficitである。
総量制約、head上界、tail上界は、scalarを定義する同じ `R` に課されている。

重みから `α=(r−1)/(n+1)` を引くと、残余は `j<n−2` で非負、
`j=n−2` で0、その先で非正になる。
非正項を落とす不等号の向きは正しく、残る項を共通上界で評価し、
台に含まれない添字を非負項で補う有限和の議論も正しい。
`R.support` にcutoffによる制限はなく、`tail_vanish` がすべての非零層を含むことを保証する。

`Resources.scalar_le_upper` は `4≤r≤n`、有理数 `e,d`、明示された資源条件の下でSO3を導く。
結論の `R.scalar ≤ upper …` は仮定に含まれていない。
`Resources.scalar_lt` はrank 4〜8の自然数シフトと角条件を保持し、
Sidon版・Apéry-pair版はBlock02の境界証拠から角条件を導いてSO5へ接続する。

## 追加検査

[ResourceChecks.lean](ResourceChecks.lean) は警告なしでコンパイルした。

1. 同じhead・tailを持つ2つの資源のscalarは、有限台の選択によらず一致することを証明した。
   `tail_vanish` によって、台へ零の層を追加しても値が変わらないことを確認できる。
2. rank 4、`e=5,d=10,n=7` で、headを4、tailの添字0〜4を各14、添字5を1とした資源を構成した。
   総量とhead上界、正の残余を持つ各tail上界が同時に飽和し、
   `R.scalar = upper 4 7 5 10 = 3451/40` が成立する。
   目標95との差はBlock01のseed `349/40` と一致する。
   従って、一般の資源に対してSO3の `≤` をそのまま `<` へ強めることはできない。

独立した有理数実装では、rank 4〜12、複数のcutoff・半整数を含むパラメータ・
cutoffを越える台について7,104件の有限資源最適化を行い、SO3と整合することを確認した。
また、総量、head上界、tail上界、tail非負性のいずれか一つを外すと、
残る条件を満たしてもSO3が破れる具体例をそれぞれ確認した。
この有限検査は補助検査であり、普遍証明はLeanの定理による。

## 合格範囲と残る接続

`Resources` の資源条件は局所仮定であり、実際の半群・接錐・cut・towerから
一つの共通資源を構成する部分は未実装。
formal scalarと実際の対象量の一致、actual Q₂の最大性からの `AperyPairData` 構成、
actualパラメータの自然数シフトへの表示も後続の接続で証明する必要がある。

rank 2・3およびrank 9以上のscalar閉鎖、Tor/Bettiへの移行、M12・P14全体は今回の合格範囲に含まない。
提出側の未完成範囲の説明は、コードの仮定と一致する。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Ordinary/Resources.lean
lake env lean tests/Resources.lean
lake env lean tests/SmallScalar.lean
lake env lean tests/Sidon.lean
lake env lean audit/DomainChecks.lean
lake env lean audit/block03/ResourceChecks.lean
python3 audit/block03/check_resource_bounds.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[有理数検査結果](resource_bound_checks.json)

[ビルド](build.log)／[ソース再検査](source_recheck.log)／[Block03テスト](tests_and_axioms.log)／[Block01回帰](block01_regression.log)／[Block02回帰](block02_regression.log)／[負のシフト検査](block01_domain_checks.log)／[追加Lean検査](resource_checks.log)
