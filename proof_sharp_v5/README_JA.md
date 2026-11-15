# NS-P14：全体証明の簡約・一本化 V05

**固有核心と新しい置換証明を展開した一本の証明稿を作成した。11pt・単段で34頁、必要付録0頁。**
主定理は元のsource、literal interval completion、各環自身の最小表示、任意体、全Betti行を保つ。
読解対象は明示取得した work commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
旧稿・本番Lean・凍結命題・既存証跡は変更していない。
V04の全49ファイルも保持し、承認された追加簡約2点を別ディレクトリの本版へ統合した。

## 最初に読む結論

- **今回の変更1：** 非antipodal第一行を、粗い体積上界と整数性で全u≥8の一つの式へ統合した。
  三剰余の正確な公式・三つの容量差・u=8第一行特例を主依存から外した。
- **今回の変更2：** 疎幅と五生成元に共通のW-HIGH補題を置き、第二行から全高次行を導いた。
  五生成元の第3–5行専用の粗上界・三基点・二項係数/u²単調性を不要にした。
- **V04の成果は保持：** antipodalの候補語による上界と整数性、N4の一つの三次式、
  ordinary算術・実核補償・actual共通接続はそのままである。
- **保持した難所：** 同jumpと同じcut資源、Tor第0補正とtop、QC→QG実核の長さ補償、PC/PG、
  元のR/Hx、SCを元offsetへ戻す段階、socle三角形の包含、幅4の全競合・両座標・実像独立、任意標数のminor。
- **ページ比較：** V04もV05も34頁の実測。今回は数学的な分岐と独立計算を減らした。
  第4章は補題の範囲を明記したため572字増えており、字数・頁数を減らしたとは数えない。
  版面・文字サイズを維持し、必要な説明を残した。

## 成果物

| 読むもの | ファイル |
|---|---|
| 一本の完全証明PDF | [NS_P14_SHARP_PROOF_JA.pdf](build/NS_P14_SHARP_PROOF_JA.pdf) |
| 編集できる単一本文 | [NS_P14_SHARP_PROOF_JA.md](NS_P14_SHARP_PROOF_JA.md) |
| 各変更の理由・Lean export・新形式化・証明状態 | [CHANGE_LEDGER_JA.md](CHANGE_LEDGER_JA.md) |
| 短縮後のDAG、A/B/C分類、全パラメータ・全行被覆 | [DEPENDENCY_AND_COVERAGE_JA.md](DEPENDENCY_AND_COVERAGE_JA.md) |
| 実測と概算の比較・組版条件 | [PAGE_COMPARISON_JA.md](PAGE_COMPARISON_JA.md) |
| 今回の独立数学レビュー | [V05_WIDTH_REVIEW_JA.md](notes/V05_WIDTH_REVIEW_JA.md) |
| 今回の統合確認 | [V05_INTEGRATION_REVIEW_JA.md](notes/V05_INTEGRATION_REVIEW_JA.md) |
| 二変更の完全な差分と形式化用statement | [V05_WIDTH_CHANGES_JA.md](notes/V05_WIDTH_CHANGES_JA.md) |
| 最新実装・証跡・形式化範囲の独立確認 | [STATUS_COVERAGE_AUDIT_JA.md](notes/STATUS_COVERAGE_AUDIT_JA.md) |
| 読解SHA・入力ハッシュ、今回の検証結果 | [SOURCE_RECEIPT.json](SOURCE_RECEIPT.json)、[verification.json](verification.json) |

新しい紙上補題は完全なstatementと証明を本文に記した。旧稿の該当箇所への参照だけで
今回固有の核心を済ませていない。不要化した成果は独立成果として既存ファイルに残り、
新稿の証明に必要な付録へ移して短く見せたのではない。

## 数学的証明と形式化の境界

この稿は指定した公刊入力を引用する紙上証明である。V04の既存レビューを継承し、
今回の二変更は別担当が仮定・全域・top・整数性を独立にレビューした。
これは外部査読や全原典の新たな再証明の認定ではない。

固定SHAのRun18は狭幅e≥5の六契約をCOMPLETEとしている。ordinary・共通端点も既存形式化がある。
一方、N4固有全域・小生成元/LTV・最終全域exportは未実装であり、
**紙上の全域証明を全域NS-P14のLean完成とは扱わない**。
新APD整数閾値、新N4高次行、ordinary任意基点の統一式の新exportは今回追加していない。
今回の非antipodal整数閾値と、共通高次行補題による五生成元consumerも新規形式化はしていない。
同じ結論への既存Lean経路がある場合も、新しい紙上経路の形式化とは分けて記録した。

今回実施したのは式の記号照合・正確算術・被覆と参照の点検・既存ハッシュの再照合である。
有限検算は本文の全称証明の代用にしていない。Leanのfresh buildは実施していない。
公刊入力は既存の版・型・使用範囲を照合した。原典全文の再取得を試みたLTVは
ネットワークのproxy 403で取得できず、未取得の本文を読んだとはしていない。

## 再現とファイル構成

`chapters/` が各章の編集元で、`checks/assemble_and_typeset.py` が単一本文とTeX/PDFを生成する。
`notes/` は詳細な採否・Lean対応・独立レビュー記録であり、数学的証明の必須付録ではない。

```sh
python3 proof_sharp_v5/checks/assemble_and_typeset.py
python3 -B proof_sharp_v5/checks/verify_reduction.py
```

作業ブランチは `proof/canonical-reduction-20261115`。今回の変更は `proof_sharp_v5/` 内の新規成果だけである。
`notes/` のV04と明記されたレビューは前版の記録であり、今回の二変更の新しい認証とは区別する。
