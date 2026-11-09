# Block01 独立監査

2026年11月9日（JST）。判定：**数値ブロックは合格。表記修正が1点ある。**

監査対象は `NS_P14_LEAN_BLOCK01_20261109.zip`。SHA-256は
`35a2b807d39e7270f7fe072e12594d00cb3f15ce0a7732f0c9cf2e3e51c9eacf`。
ZIP内の証明・テスト・検証記録は変更せず収録した。

## 確認結果

- 元のmanifestにある14ファイルのSHA-256がすべて一致。
- 固定した9依存のコミットがすべて一致。
- Lean v4.36.0-rc2、mathlib `139105d28c7685a154cb3093f79edb2e16708099` で、キャッシュを使わず依存から再ビルド。1980ジョブが成功。
- ソース再検査・境界テストも終了コード0。
- 5行の数値と必要な符号条件は、独立した有理数計算でも一致。
- 対象10定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。保存された公理ログとも一致し、`sorryAx`・追加の数学的公理への依存はない。

## 表記修正

元の報告および `SmallScalar.lean` の `small_gap_pos` 直前のコメントにある
「任意の整数シフト」「all integer shifts」は、正値性の範囲を広く読める。
正確な範囲は次のとおり。

| 定理 | 範囲 |
|---|---|
| `gap_shift` | 任意の有理数シフト `s,t : ℚ` に対する恒等式 |
| `small_gap_pos` | `4 ≤ r ≤ 8`、非負整数シフト `s,t : ℕ`、かつ `r ≤ 5 ∨ s+t ≠ 0` での正値性 |

rank 4で `s=-4,t=0` とすると、`e=1,d=10` で `gap=-121/56<0` になる。
[DomainChecks.lean](DomainChecks.lean) で、この値と全整数に対する正値性の否定をLeanで確認した。
証明本体は正しい範囲に限定されている。原本との照合を保つため、元のコメントは変更していない。

## 合格範囲と残る接続

合格範囲は、提出された定義に対する数値ブロックの内部整合性と再コンパイル。
参照先の原稿 `auditability_search/ORDINARY_PAPER_REDUCTION_JA.md` はZIPに含まれず、
原稿SO3–SO5との式の対応は未確認。

後続ブロックでは、実対象から自然数シフトの表示、rank 6–8の角の除外、
および実際のscalar `F` に対する `F ≤ upper …` を供給する必要がある。
actual Apéry–Sidon、資源上界、Bettiへの移行、M12・P14全体は今回の合格範囲に含まない。

## 記録

- [監査結果](review.json)
- [ビルドと再検査の終了コード](replay.json)
- [依存からのビルドログ](build.log)
- [ソース再検査ログ](source_recheck.log)
- [境界テストと公理依存ログ](tests_and_axioms.log)
- [負のシフトの反例検査ログ](domain_checks.log)
- [独立した有理数計算](arithmetic_check.json)
- [元ファイルのハッシュ照合](hash_check.json)
- [依存コミットの照合](dependency_revisions.json)
