# Run13 continuation 独立レビュー

reviewer: `/root/run13_final_continuation_review`。current worktree（基準Run12 6b8d168、途中HEAD92cbe8f、未commit継続）をread-onlyで確認。
Criticalなし。Importantは2件。

1. `GradedBaseChange`は正しい拡大grading L⊗Kₜを与え、actual changed Koszul Hの直和分解まである。
   ただしactual係数変更isoによって、これを別途構成した`fullGGrading L` / `actualT/A/N/QGrading L`の
   gradedKoszulComplexへ同定する宣言がない。actual L側のgraded Betti不変性を閉じること。
   必要な結論はextendedGradedKoszulComplex≅actual L gradedKoszulComplex（total複体へのinclusionと可換）。
   単にtargetへtransported gradingを設置する対応は不可。
2. `tests/KoszulExactness.lean:6`がModuleCatのuniverseを独立に推論し、ModuleCat.{0}を要求するgeneric theoremへ適用できない。
   intended universeを明示し、受入検査と全公理監査まで通すこと。

既存証明の評価：実自由解消/通常Tor比較/自然性、実syzygy rank橋、有限homology（無限chainをfiniteと仮定しない）、
actual order gradingとsame-jump t→t+s、実L[X]作用とactual変数行列、全ideal初項の基底、±1 minor、環境宣言auditは妥当。

Declined to judge（執行側rulingで整理する）：
- 極小自由解消の存在：今回どの定理も存在を使わず、given resolutionの橋でよい。
- 全対象Tor/Tor' balancing：syzygy LESで必要なrank橋を供給済み。
- actual cut/localization-rank0/tower/connecting-rank/harmonic initial ideal：後続runが供給する対象の入力。
- 公刊入力/最終P14：Run13の範囲外。
- 最終ZIP/progress/commit/push/remote-clean：レビューと検証後に執行側で実行。

判定：With fixes。上記2件を同じRun13の1 fix passで閉じ、全suiteを再実行する。再レビューを追加しない。

## 同じfix passでの対応

Important1：`KoszulScalarComponents`で既存total比較のinl/inr式、`GradedScalarComparison`で実piece比較、
`GradedScalarKoszul.gradedScalarKoszulIso_commutes`でtotal比較・inclusion可換性を証明。
`ActualGradedBaseChange`は独立した既存のfullGGrading L / actualT/A/N/QGrading Lを使い、
五つのgraded複体同型とactual graded Betti保存を供給した。target gradingの置換はしていない。
`tests/ActualGradedBaseChange.lean`は標数2→RatFuncでこの五つを検査し、RED→GREEN。

Important2：テストのintended universeをModuleCat.{0}で明示しRED→GREEN。
修正後core build143は4958jobs成功。最終の全suite・環境公理監査の結果は検証JSONを参照。
独立レビューを追加で派遣せず、このfix passのTDDと全検証で閉じる。
