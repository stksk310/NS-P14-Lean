# Run19 原稿へ戻す証明差分

元のS、元の向き、同じactual QC/R、任意体、literal interval targetと双方の最小変数を全出口で保持する。

| 原稿の箇所 | Lean の実証明 | 原稿へ反映する差分 |
| --- | --- | --- |
| N2 距離・socle三角形 | CoreWords/SocleTriangle/Distance | actual最小語との全単射、同じQCの全三角形を明示 |
| N3 純語・混合語 | StandardWords | 純語もSCで統一。gcd別分岐を削除可能。元R=0はu≤5まで強化 |
| N4 三行 | CubicPayment/HigherRows | 新cubicの係数36,140,45,4、u≥6、比8T3/10T4をそのまま使用。u5は(18,7,0)へ強化 |
| N5 第一行 | Relations/FirstCount/FirstLarge | Eのguard保持。奇数のfloorを捨てた弱い有理包絡でも支払い成立 |
| N6 小幅 | SmallWidths | u4のPC+sigma≤5を同じdownsetで同時評価 |
| N7 幅4全m | WidthFourCore/Competitors/Initial/Comparison | 全j・両座標から消滅閾値を導く。内部重みの停止正規化＋actual像独立性で直接9生成元kernel等式。不要生成元を除いて6/8/8/6。一般のinitial-ideal変形定理は不要 |
| 一・二生成元 | SmallEmbedding.Base/IntervalCompletionAll | e1の幅0にもliteral closureを無条件定義。e2は実AP表示から(1,1,0,...) |
| 三生成元/LTV必要比較 | ThreePresentation/LanTuVu/ThreeComparison | 下記の直接証明へ差替え可能。原典の強い線形上界を証明したとは書かない |

## 三生成元の新しい直接証明

正の内部文字数の共通端点機構を構成し、既存52 moduleの各証明を弱い非空条件へ再適用した。旧公開APIは変更しない。全競合の最小点のうちL=0は各剰余に高々1個。L>0の最小点は元の実最小語pとj≥1のforbiddenStartであり、元の高さからj−1<(L_p−2)+。この割当を選んでも(p,j−1)から競合点を復元できるため単射。従ってR≤Σp(L_p−2)+。

内部一文字なら全最小語はy^n、n<uで次数が単射。PC≤u、(L_p−2)+≤(n−3)+、R≤Σn<u(n−3)+=C(u−3,2)。一変数QCのEuler式はBetti=(1,1)。既存のactual補償付きTorからβ1≤PC+R+1、β2≤PC+2R、β3≤R、上の行は0。u≥3でこれをliteral targetの下界へ払う。u=2はfull AP。幅≥m−1は既存ordinary全行定理を使用する。CM、gcd(m,u)=1、特性の追加仮定はない。

これは必要なLTV比較契約の独立な実証明であり、原典のμ≤s+1等の三つの強い線形数値上界・Herzog分類・一般Gröbner変形を形式化したという意味ではない。原稿の引用を残す場合も、Leanとの一致はこの比較範囲で記載する。

全P14の分割と主定理合成はRun20へ渡す。本文N4/V06の固定hash・入口・凍結10型はRUN19_INPUT_INVENTORY_JA.md/RUN19_V06_LEMMA_MAP_JA.mdおよびsources receiptを参照。
