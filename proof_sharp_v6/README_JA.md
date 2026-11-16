# NS-P14：全体証明の簡約・一本化 V06

**固有核心と新しい置換証明を展開した一本の証明稿を作成した。11pt・単段で34頁、必要付録0頁。**
主定理は元のsource、literal interval completion、各環自身の最小表示、任意体、全Betti行を保つ。
読解対象は明示取得した work commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
旧稿・本番Lean・凍結命題・既存証跡は変更していない。
V04の全49ファイルとV05の全55ファイルを保持し、承認された追加簡約2点を別ディレクトリの本版へ統合した。

## 最初に読む結論

- **今回の変更1：** 全ての長い競合による実核を保ち、必要な高さ上界・有限生成性・純v冪を直接証明した。
  周期による具体的停止回数とcarry五場合の表を主証明から外した。
- **今回の変更2：** denseのt3／t≥4を、一つの非負係数式でt≥3へ統合した。
  t2／t≥3の二枝になり、q4/t3の等号も同じ式に含まれる。
- **前稿の成果は保持：** 非antipodal第一行の整数性、W-HIGH共通化、antipodalの候補語、
  N4の一つの三次式、ordinary算術・実核補償・actual共通接続はそのままである。
- **保持した難所：** 同jumpと同じcut資源、Tor第0補正とtop、QC→QG実核の長さ補償、PC/PG、
  元のR/Hx、SCを元offsetへ戻す段階、socle三角形の包含、幅4の全競合・両座標・実像独立、任意標数のminor。
- **ページ比較：** V04・V05・V06とも34頁の実測。今回は周期計算と場合分けを不要にした。
  Markdown本文はV05比92字増（端点60字、幅32字、式記法を含む）。有限性と境界の根拠を
  明示した増加であり、字数・頁数を減らしたとは数えない。版面・文字サイズは維持した。

## 成果物

| 読むもの | ファイル |
|---|---|
| 一本の完全証明PDF | [NS_P14_SHARP_PROOF_JA.pdf](build/NS_P14_SHARP_PROOF_JA.pdf) |
| 編集できる単一本文 | [NS_P14_SHARP_PROOF_JA.md](NS_P14_SHARP_PROOF_JA.md) |
| 各変更の理由・Lean export・新形式化・証明状態 | [CHANGE_LEDGER_JA.md](CHANGE_LEDGER_JA.md) |
| 短縮後のDAG、A/B/C分類、全パラメータ・全行被覆 | [DEPENDENCY_AND_COVERAGE_JA.md](DEPENDENCY_AND_COVERAGE_JA.md) |
| 実測と概算の比較・組版条件 | [PAGE_COMPARISON_JA.md](PAGE_COMPARISON_JA.md) |
| 今回の独立数学レビュー | [V06_MATHEMATICAL_REVIEW_JA.md](notes/V06_MATHEMATICAL_REVIEW_JA.md) |
| 今回の統合確認 | [V06_INTEGRATION_REVIEW_JA.md](notes/V06_INTEGRATION_REVIEW_JA.md) |
| 二変更の完全な差分と形式化用statement | [V06_ENDPOINT_CHANGES_JA.md](notes/V06_ENDPOINT_CHANGES_JA.md)、[V06_DENSE_CHANGES_JA.md](notes/V06_DENSE_CHANGES_JA.md) |
| 最新実装・証跡・形式化範囲の独立確認 | [STATUS_COVERAGE_AUDIT_JA.md](notes/STATUS_COVERAGE_AUDIT_JA.md) |
| 読解SHA・入力ハッシュ、今回の検証結果 | [SOURCE_RECEIPT.json](SOURCE_RECEIPT.json)、[verification.json](verification.json) |

新しい紙上補題は完全なstatementと証明を本文に記した。旧稿の該当箇所への参照だけで
今回固有の核心を済ませていない。不要化した成果は独立成果として既存ファイルに残り、
新稿の証明に必要な付録へ移して短く見せたのではない。

## 数学的証明と形式化の境界

この稿は指定した公刊入力を引用する紙上証明である。V04・V05の既存レビューを継承し、
今回の二変更は別担当が全j・有限性・零剰余・denseの等号境界・topを独立にレビューした。
これは外部査読や全原典の新たな再証明の認定ではない。

固定SHAのRun18は狭幅e≥5の六契約をCOMPLETEとしている。ordinary・共通端点も既存形式化がある。
一方、N4固有全域・小生成元/LTV・最終全域exportは未実装であり、
**紙上の全域証明を全域NS-P14のLean完成とは扱わない**。
新APD整数閾値、新N4高次行、ordinary任意基点の統一式の新exportは今回追加していない。
V05の非antipodal整数閾値と共通高次行consumer、今回のceiling経由の有限性とdenseの統一も新規形式化はしていない。
同じ結論への既存Lean経路がある場合も、新しい紙上経路の形式化とは分けて記録した。

今回実施したのは式の記号照合・正確算術・被覆と参照の点検・既存ハッシュの再照合である。
有限検算は本文の全称証明の代用にしていない。Leanのfresh buildは実施していない。
公刊入力は既存の版・型・使用範囲を照合した。原典全文の再取得を試みたLTVは
ネットワークのproxy 403で取得できず、未取得の本文を読んだとはしていない。

## 再現とファイル構成

`chapters/` が各章の編集元で、`checks/assemble_and_typeset.py` が単一本文とTeX/PDFを生成する。
`notes/` は詳細な採否・Lean対応・独立レビュー記録であり、数学的証明の必須付録ではない。

```sh
python3 proof_sharp_v6/checks/assemble_and_typeset.py
python3 -B proof_sharp_v6/checks/verify_reduction.py
```

作業ブランチは `proof/canonical-reduction-20261115`。今回の変更は `proof_sharp_v6/` 内の新規成果だけである。
`notes/` のV04・V05と明記されたレビューは前版の記録であり、今回の二変更の新しい認証とは区別する。
