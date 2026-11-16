# Run16 原稿対応・証明変更台帳

基準は Run15 `447b7ae782414b739968a2a3009dd3a52ae230d0`。指令は `0cda4e8597ea1bafa8770b851ff2373973ee0e03` の Run16 文書。ここでの変更は将来の原稿へ戻すための記録であり、原稿本文を既に改訂・公刊したという意味ではない。

| ID | 同じactual sourceからの入口・主要証明 | 後続向け出口 |
|---|---|---|
| I_NORMALIZE | `Semigroup.WidthNormalization/CarrierTransport`, `Endpoint.Normalization`。EHでは元のm,d,a,uを保持。狭幅では同じcarrierを正規化 | 実際の次数付き代数・完備接錐・元の最小表示のBettiへ戻る同値 |
| E_CORE | `Core/Map/Kernel/Words`。整数対(n,B)の実加法monoid、実単項式写像、最大原子分解長 | C→Gの全射、全長い表示による正確な線形核 |
| E_COORD | `Fibers/IdealCoordinates/FiberModule/Quotient`。E=k[x,v]上の実際の作用と基底係数を照合 | C≃⊕M_r、G≃⊕M_r/(M_r∩T_r) のE加群同型 |
| E_KERNEL | `Competitors/Carry/ActualKernel/AssembledKernel`。すべてのj≥1、整数clampを使う | N_r=M_r∩T_r。Tだけを核に置き換えない |
| E_STOP | `MinimalWords/Bounds/Residues/Stopping`。極小点は純内部語、長さ<u。周期u/gcd(m,u) | J0=(u−2)/2から周期一つを追加した正確な停止。m,u互いに素は不要 |
| E_BOUNDS | `CarrySums/CompetitorBounds/SocleInjection/SocleBounds` | R≤Σz_r≤W−u、R≤u max(Hx−2,0)、Rhat=min。向きは固定 |
| E_HOMOLOGY | `HomologyFinite/Balance/ArtinQuotient/Socle` | 実E-Koszul homologyの次元(P_G,P_G+R,R)、上次数0、R=実同時annihilatorの次元 |
| E_TRANSFER | `VariableOrder/NativeTransfer/Compensation/FullTransfer` | q内部変数とq+2全変数を区別した、核補償付き全行Tor評価。i=0をguard |
| E_ARTIN | `StandardArtinGrading/Finite/Generation/Generators/Rows`, `ArtinRank/Weights` | 一般の実斉次Artin商でh0=1,h1=q、総次元、有限台、b1=実idealのTor0、三つの第一行評価、q=5の差14、全正次数minor評価 |
| E_ROW | `FirstRow/PositiveRows/RowPackage` | 一般qの全行、floorの型と減算の加法形、β0=1、top≤Rhat、上次数0。元の狭幅完備接錐へ直接適用 |
| E_TWO | `InternalMonoid/TwoMonomial/InternalCoordinates/TwoInternal/TwoRows` | q=2だけの実単項式核、実内部作用、σ_C、(1,σ_C+1,σ_C)、四行R版/Rhat版 |

## 原稿へ反映すべき証明経路

第一Artin評価は新たにparent/child計数を重複実装せず、Run15の `generated_harmonic_bound` のj=1から導いた。この既存定理は実初期加群・標準単項式・実Koszul rankから証明されている。今回、任意の真の斉次ideal I（I1=0、T/Iは有限次元）について、実除法の正規形が次数を保つこと、実商の基底・次数分解・単位による次数0生成、augmentation、b0=1を構成した上で適用している。原稿IV.21の証明は、このより一般的な調和型補題への帰着として書き直せる。

`artinFirstIdealIso` は実完全列0→I→T→T/I→0のconnecting mapの同型である。`idealGeneratorNumber` は実際のIのH0=Tor0を用いる。既存の `koszulH0Equiv` はこのH0を実変数作用の生成する部分加群による商 I/(y)I と同定するので、ここでのμはそのNakayama fibreの次元という標準次数付きの定義である。任意の非斉次idealについて大域的最小生成集合を新たに構成したとの主張はしない。一般の生成元数を数値仮定として渡していない。第一行の符号付き差はℚ上で表現し、高次数の負係数をNat減算で消していない。

端点socleの上界の証明では、実単射M/(M∩T)→E/TからTの角へ注入する。さらに `SoclePoints/SocleCorePoints/SocleCorners` が実socleの全基底をM内のNの角と同定し、`AdjacentCorners` が隣接極小点(a,b)から角(b_1−1,a_2−1)を復元する。E/NやE/T全体のArtin性は使わない。

q=2のArtin Betti profileは、有限長実QCの二変数Koszul Eulerと内部同時annihilatorから導出した。この導出自体は単項式性を入力にせず、別途q=2の実単項式核を証明している。一般qでQCが単項式T商であるとは主張しない。三内部変数の生存関係 y_2 y_4=y_3² を受入試験で保持する。

`FiniteWords/Minima/Order/Survivors/SocleWindow` は探索モデルと実対象をつなぐ形式定理である。具体的なPC/PG/Rの値はこの定理の後でLeanの`decide`により検証する。`native_decide`や数値結果の公理化は用いない。有限例は一般証明を置換しない。

## 型と有限性

Eは端点の2変数環、Tは内部のq変数環、全最小表示はq+2変数環。GとCはE有限で、v^m=0からGのE-rankは0。Gのk有限次元性は仮定しない。有限性を使うのは実homology・QC/QG・実socle・有限加群のTorなど、個別に証明した対象だけである。

PCとPGは別の実商の次元。差PC−PGは実核完全列から非負性を証明してから使う。全行補償とNat減算の加法形を保持する。内部σ_Cと端点Rは異なる環・異なる作用のannihilatorである。
