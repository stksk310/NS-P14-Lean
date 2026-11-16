# V06 N4：公開本文から確定したRun19の数学的入口

2026-11-15 JST。資料公開commitは `a7504eea25f02728d1be6cd0082e8484d639dbe2`。
本書は本文と既存Leanの入口の照合、およびRun19指令の具体化である。N4の新しいLean証明・cold build・公理probeを実施したという記録ではない。

## 固定資料と確認範囲

| 資料 | SHA256 |
|---|---|
| [N4本文N0–N8](../../../proof_sharp_v6/chapters/05_N4_JA.md) | `cd6236f6b16d5de7998064e66d566f5c6522c8a943d040ec6242a18dde2194c5` |
| [全体本文](../../../proof_sharp_v6/NS_P14_SHARP_PROOF_JA.md) | `fe8271bbaabf6b3d31243628c3a5a5a305b82361c794f03c6e13a2fe98c72791` |
| [N4形式化対応・未形式化範囲](../../../proof_sharp_v6/notes/N4_AUDIT_JA.md) | `92c4b5b32776c5eb5bd53a2d3ad651441de71898be52fd8a9bae1ca778268f64` |
| [V06 ZIP](../../../proof_sharp_v6/NS_P14_SHARP_V06.zip) | `788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d` |

N4章全体、共通章BRIDGE/CAP/MINCAP、最終合成章§6.1–6.3、N4監査ノート、同期引継ぎの範囲を読んだ。N4章が全体本文に同じbytesで含まれることも確認した。全体本文の他の専門章や公刊原典を全て再監査したという範囲ではない。

ZIPは52 entry・51 payloadの全hash・厳密な被覆・CRCを確認し、候補として共有されていたSHAと実物の一致を確認した。公開manifestの136 entryも全件一致した。資料公開差分は既存準備commit `3cf5e157fa7bb85831de2eb0b202183abd81b1d3` を継承し、Lean・tests・audit・scripts・固定依存に変更を加えていない。

## N0／N1b：同じactual sourceの四行

`0<a<b<u`、`d≥1`、`gcd(a,b,u)=gcd(m,d)=1`、`m≥d*u+2`。物理幅は`V=d*u`、係数体kは任意である。

Pは実QCの次元、sigmaは同じQCの内部socle、Rは元のactual Gの端点socle。N1a/N2から `P≤W`、`R+u≤W`、`sigma≤u−1`、`W≤1+floor(u²/4)`を供給する。

```text
β1 ≤ P+sigma+1+R
β2 ≤ 2P+sigma+3R
β3 ≤ P+3R
β4 ≤ R
```

これらの形式化済み入口は `NSP14.Endpoint.Data.actual_two_row_one/two/three/four`。`actual_two_all_rows`はRhat版なので、actualR版と取り違えない。RをRhatで上から評価する場合も元の向きの不等式を明示する。

## N4a：actual行の有理上界

以下の数値関数はℚ値として扱う。係数体内の除法ではない。

```text
U2(u) = 5*u^2/4 - 2*u + 4
U3(u) = u^2 - 3*u + 4
U4(u) = u^2/4 - u + 1
T_i(u) = i * Nat.choose u (i+1)
```

N1bと同じP/sigma/R/Wを使い、加法形の資源評価から

```text
β2 ≤ 5*W - 2*u - 1 ≤ U2(u)
β3 ≤ 4*W - 3*u     ≤ U3(u)
β4 ≤ W - u        ≤ U4(u)
```

を得る。中間の引算はℚの通常の引算または等価な加法形にする。N4aのactual接続を未証明入力にした数値consumerだけでは不十分である。

## N4b／N4c：u≥6の一つのcubicと比

u=6+z、z:Natとする。新しい恒等式は正確に

```text
12*(T_2(u)-U2(u)) = 4*z^3 + 45*z^2 + 140*z + 36 > 0.
```

である。旧第2行下界 `T_2(u)+u` の差の `152*z+108` を使わない。

```text
U2-U3  = u^2/4+u > 0
U2-5*U4 = 3*u-1 > 0
T_3/T_2 = 3*(u-3)/8 ≥ 1
T_4/T_2 = (u-3)*(u-4)/10 ≥ 1/5
```

比の分母T_2はu≥6で正。Leanでは次の交差積と正係数の式で証明してもよい。

```text
8*T_3 = 3*(u-3)*T_2
10*T_4 = (u-3)*(u-4)*T_2
T_2 ≤ T_3,  T_2 ≤ 5*T_4
```

従って `β2≤U2≤T_2`、`β3≤U3≤U2≤T_2≤T_3`、`5*β4≤5*U4≤U2≤T_2≤5*T_4`。
最後にN4c直後の `F_i(m,V)≥T_i(V)≥T_i(u)`を実interval completionのcapacity APIで供給し、元の完備接錐へ運ぶ。

このN4経路は個別のU2/U3/U4の大小と二項係数比による。先行V06同期のfive/sparse向け共通higher wrapperへ接続することはN4の要件ではない。異なる資源包絡をN4に強制してu=6の適用を失わない。

境界u=6では `T=(40,45,24)`、`U=(37,22,4)`、cubic右辺36。独立に五つの多項式恒等式（cubic・Uの二差・Tの二交差積）をSymPyで展開照合した。普遍性のLean認証はこれからRun19で行う。

## N4の小幅

| u | 元sourceの第2–4行上界 | actual target最小値／処理 |
|---:|---|---|
| 5 | (24,13,2) | (25,25,9) |
| 4 | (12,5,0) | (12,7,1) |
| 3 | (8,3,0) | d=1はsource=target、d≥2はV≥6で払う |

u=5は`W≤1+floor(25/4)=7`からP≤7・R≤2、sigma≤4を使う。u=4はP≤5・sigma≤2・R=0。u=3は同じQCを`k[y,z]/(y,z)^2`へ接続する。

u=4の**target自身の第4行の最小値は1**であり、source上界0と混同しない。u=3,d=1は粗いu容量では払わずliteral carrier一致を使う。V06の一般target profileから、各小幅と全V≥uへの単調性を証明する。

## 残るN4核心とRun19への対応

N2の実downset／socle三角形、N3のSCから元offset・heightへの帰還は未形式化の接続を含む。N5の三関係・guard付き矩形計数、N6の小幅第一行、N7の全j・両座標・非禁止像独立性、N8の全域合成もRun19の担当である。N4bだけのLean化をN4全域完成と数えない。

原稿N5–N7は旧指令で保持した数学的経路と整合する。Run19は新cubicの正確な出口とactual接続を追加し、小幅・全mの証明を引き続き実装する。先行同期五項目とRun19数学の完了は別であり、資料公開commitは先行同期の完了証跡ではない。

本照合の範囲では修正が必要な数学的破綻は見つからない。資料内の既存レビュー判定を、新しいLeanの検証結果として転用しない。

再照合したsource hash・Git binding・ZIP・小幅capacity・五恒等式と、書込みなしの算術検査の終了コードは[今回のreceipt](../../../verification/run19/planning/v06_n4_publication_20261115/receipt.json)に保存した。[算術検査の生出力](../../../verification/run19/planning/v06_n4_publication_20261115/published_math_only.json)は22 symbolic identities、366959 finite transcription checks、6660 partition sanity casesを記録する。
