# NS-P14：全体証明の簡約・一本化 V04

**固有核心と新しい置換証明を展開した一本の証明稿を作成した。11pt・単段で34頁、必要付録0頁。**
主定理は元のsource、literal interval completion、各環自身の最小表示、任意体、全Betti行を保つ。
読解対象は明示取得した work commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
旧稿・本番Lean・凍結命題・既存証跡は変更していない。

## 最初に読む結論

- **最も効く数学的変更：** antipodalは候補語のspanningによるP上界と調和評価だけで足りる。
  exact presentation・P/W/b1の等式を主依存から外し、整数性でh=4/h≥5も一式へ統一した。
- **N4高次行：** 一つの三次式と二項係数比で第2–4行を払い、四次・五次式を不要にした。
- **全体の短縮：** actual接続をBRIDGEへ集約。ordinaryのtarget余剰全式・調和凸性経路・床の偶奇分岐、
  端点のexact N角算出、sparse第二行の同型分岐を、それぞれ必要な不等式へ置き換えた。
- **保持した難所：** 同jumpと同じcut資源、Tor第0補正とtop、QC→QG実核の長さ補償、PC/PG、
  元のR/Hx、SCを元offsetへ戻す段階、socle三角形の包含、幅4の全競合・両座標・実像独立、任意標数のminor。
- **ページ比較：** 新稿34頁は実測。現行経路の重複なし一本化は約39–45頁の概算。
  比較資料本45頁の実測を、そのまま「厳密に11頁削減」とは数えない。

## 成果物

| 読むもの | ファイル |
|---|---|
| 一本の完全証明PDF | [NS_P14_SHARP_PROOF_JA.pdf](build/NS_P14_SHARP_PROOF_JA.pdf) |
| 編集できる単一本文 | [NS_P14_SHARP_PROOF_JA.md](NS_P14_SHARP_PROOF_JA.md) |
| 各変更の理由・Lean export・新形式化・証明状態 | [CHANGE_LEDGER_JA.md](CHANGE_LEDGER_JA.md) |
| 短縮後のDAG、A/B/C分類、全パラメータ・全行被覆 | [DEPENDENCY_AND_COVERAGE_JA.md](DEPENDENCY_AND_COVERAGE_JA.md) |
| 実測と概算の比較・組版条件 | [PAGE_COMPARISON_JA.md](PAGE_COMPARISON_JA.md) |
| 最終統合レビュー | [FINAL_INTEGRATION_REVIEW_JA.md](notes/FINAL_INTEGRATION_REVIEW_JA.md) |
| 最新実装・証跡・形式化範囲の独立確認 | [STATUS_COVERAGE_AUDIT_JA.md](notes/STATUS_COVERAGE_AUDIT_JA.md) |
| 読解SHA・入力ハッシュ、今回の検証結果 | [SOURCE_RECEIPT.json](SOURCE_RECEIPT.json)、[verification.json](verification.json) |

新しい紙上補題は完全なstatementと証明を本文に記した。旧稿の該当箇所への参照だけで
今回固有の核心を済ませていない。不要化した成果は独立成果として既存ファイルに残り、
新稿の証明に必要な付録へ移して短く見せたのではない。

## 数学的証明と形式化の境界

この稿は指定した公刊入力を引用する紙上証明である。専門章同士の相互レビューと
最終接続レビューでは、読解範囲に未解消の数学的指摘は残っていない。
これは外部査読や全原典の新たな再証明の認定ではない。

固定SHAのRun18は狭幅e≥5の六契約をCOMPLETEとしている。ordinary・共通端点も既存形式化がある。
一方、N4固有全域・小生成元/LTV・最終全域exportは未実装であり、
**紙上の全域証明を全域NS-P14のLean完成とは扱わない**。
新APD整数閾値、新N4高次行、ordinary任意基点の統一式の新exportは今回追加していない。
同じ結論への既存Lean経路がある場合も、新しい紙上経路の形式化とは分けて記録した。

今回実施したのは式の記号照合・正確算術・被覆と参照の点検・既存ハッシュの再照合である。
有限検算は本文の全称証明の代用にしていない。Leanのfresh buildは実施していない。
公刊入力は既存の版・型・使用範囲を照合した。原典全文の再取得を試みたLTVは
ネットワークのproxy 403で取得できず、未取得の本文を読んだとはしていない。

## 再現とファイル構成

`chapters/` が各章の編集元で、`checks/assemble_and_typeset.py` が単一本文とTeX/PDFを生成する。
`notes/` は詳細な採否・Lean対応・独立レビュー記録であり、数学的証明の必須付録ではない。

```sh
python3 proof_sharp_v4/checks/assemble_and_typeset.py
python3 -B proof_sharp_v4/checks/verify_reduction.py
```

作業ブランチは `proof/canonical-reduction-20261115`。今回の変更は `proof_sharp_v4/` 内の新規成果だけである。
