# Run19 V06補題・凍結出口対応

| ID | V06／必要契約 | 実装領域 | 最終出口 |
| --- | --- | --- | --- |
| N_DISTANCE | N2、実標準語downset/card、全socle三角形、4(W−1)≤u²、sigma≤u−1 | CoreWords/SocleTriangle/Distance | distance_closed |
| N_WORDS | N3、純軸≤u−2、混合2(s+t)≤u、元のHx≤u−3、u≤4で元R=0 | StandardWords | words_closed |
| N_HIGH | N4a–c、u≥6の新cubicと比、小幅u3/4/5、元source高次全行→literal target | CubicPayment/HigherRows | high_closed |
| N_FIRST | N5、guard付きP計数・sigma上界、u5とu≥9のactual第一行 | Relations/FirstCount/FirstLarge | first_closed |
| N_SMALL | N6、u3/5/6/7/8、u4の通常対とd≥2、任意m/d/Field全行 | SmallWidths | small_closed |
| N_WIDTH4 | N7、d1u4a1b3全m≥6、全j両座標・制限anchor・initial ideal・actual独立性 | WidthFour* | width4_closed |
| N_CLOSE | N8、元S e4狭幅全行、独自の最小変数と完備接錐 | Comparison | narrow_four_closed |
| I_BASE | e≤2、無条件literal interval completionを含む全行比較 | IntervalCompletionAll/SmallEmbedding.Base | base_closed |
| X_LTV | 必要なLTV契約：理想から一段shiftした商の全正行比較 | ThreePresentation/LanTuVu | ltv_closed |
| I_THREE | 元S e3全幅、第0/消滅後を含む全行比較 | ThreeComparison | three_closed |

X_LTVは本runのconsumerに必要な比較版を凍結する。原典Theorem1.1の別の三つの強い数値上界を、この比較契約から形式化済みとは称さない。これは主張を弱めた完成wrapperではなく、必要公刊入力の正確な使用版と商へのshiftの分離である。追加の比較結論を入力にしない実証明が必要である。

旧N_HIGHの四次／五次補題と+V払い戻しは新主経路に不要。旧196組証書と有限m上限は導入しない。N2/N3/N5/N6/N7は原稿どおり必要。先行V06五項目の認証はそのまま保存し、Run19の成果に再分類しない。
