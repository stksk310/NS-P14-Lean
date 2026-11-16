# Block01 独立監査への対応

2026年11月9日（JST）。監査元は `audit/block01-20261109` の
commit `a4acb316c4c5876a854c570369cdfb45e463ce8a`。
その `audit/` 以下を内容を変えずに取り込んだ。監査ブランチは初期mainから派生しており、
古いBlock01スナップショットで現行Block02を上書きしないよう、監査資料だけを取り込む。

## 指摘と修正

判定は `PASS_NUMERICAL_BLOCK_WITH_DOCUMENTATION_CORRECTION`。
指摘は `small_gap_pos` 直前のコメントにある「all integer shifts」。
定理の型は最初から `s,t : ℕ` と角条件を要求しており、証明の欠落ではなかった。

| 主張 | 正確な範囲 |
|---|---|
| `gap_shift` の恒等式 | 任意の有理数シフト `s,t : ℚ` |
| `small_gap_pos` の正値性 | `4 ≤ r ≤ 8`、`s,t : ℕ`、`r ≤ 5 ∨ s+t ≠ 0` |

ソースコメント、監査引継ぎ、進捗、Block01の説明をこの範囲に揃えた。
定義・定理の型・証明本体は変更しない。

## 再検証

両ブロックの検証スクリプトへ監査の `audit/DomainChecks.lean` を追加した。
これはrank 4で `s=-4,t=0` の値が `-121/56` になることと、
全整数シフトへの無条件の正値性が偽であることをLeanで検査する。
元の10件・14件の公理依存検査とBlock01の回帰テストも維持する。

```sh
python3 scripts/verify_block01.py
python3 scripts/verify_block02.py
```

現行の結果は `verification/block01/verification.json` と
`verification/block02/verification.json`、各ログに記録する。
現行manifestは修正後のソース・スクリプト・記録へ更新する。
`audit/` の監査原本、既存ZIP、初回依存ビルドのログは当時の記録として保持する。
Block02のソース照合は、更新されたBlock01 manifestとの一致を意味し、
初回提出ZIPとのバイト単位の不変性とは区別する。

原稿SO3–SO5との式の対応、actual Q₂からのApéryデータ構成、SO3資源上界、
Tor/Betti、M12・P14全体は今回の監査合格や表記修正で完了したとは扱わない。
