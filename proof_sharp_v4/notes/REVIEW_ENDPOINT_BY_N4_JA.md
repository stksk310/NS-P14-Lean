# 端点章の独立レビュー（N4担当）

レビュー対象：`proof_sharp_v4/chapters/03_ENDPOINT_JA.md` の全文。
照合した基準 source は commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
本レビューでは対象章を変更せず、Lean/lake の再実行もしない。

**判定：確認した証明経路に、結論を阻む gap、追加仮定、任意標数性の欠落を検出しなかった。**
これは対象章の紙上論証と列挙した既存実装の接続の読解レビューであり、
本章全体を新たに Lean kernel で認証したとの意味ではない。

## 照合資料

- V02 `proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md` §12.1–12.9。
- `auditability_search/LATER_READABILITY_AUDIT.md` §§1,7。
- `NSP14/Endpoint/Competitors.lean` の `longer_core_pair`, `core_dead_iff_competitor`。
- `Stopping.lean` の周期・停止と `competitorFiber_stopping`。
- `CarrySums.lean` の `carry_sum_one`, `residueCeiling_sum`, `wordVolume_coordinates`。
- `SocleBounds.lean` の `actualR_le_sum_z`, `actualR_le_volume`, `actualR_le_height`, `actualR_le_Rhat`。
- `Compensation.lean` の実短完全列、`QKernel_dimension`, `actual_kernel_compensation`。
- `FullTransfer.lean` の `compensation_merge`, `actual_core_endpoint_bound`,
  `completed_core_endpoint_bound`, `actual_endpoint_top`。
- `FirstHarmonic.lean` の `QCore_first_harmonic`。
- `ArtinRank.lean` の `positive_artin_rank_sum`, `QCore_positive_betti_add`。
- `TwoMonomial.lean` の `two_internal_monomial_kernel`, `two_internal_kernel_ideal`、
  `TwoInternal.lean`, `InternalSocleBasis.lean`, `TwoRows.lean`。

## 核・資源・移行の検査

|検査項目|具体的な確認|判定|
|---|---|---|
|E-CORE の source と最小性|長い表示の式から \(l-1=jd\), \(a-B=jm\ge m>u\) を導く。\(du<m\) を隠れて用いていない。二つの gcd 条件が生成元全体の gcd 1 を与える|成立|
|E-KERNEL の全競合|\(\gcd(m,d)=1\) から長さ差が \(jd\)、offset 差が \(jm\) と強制される。\(j=1\) だけへ縮めていない|成立|
|clamp と実核|長い側を上方へ動かすことで短い第一座標の負値を0へ補える。第二座標は \(c\ge1\) により非負。短い側が actual core にある条件が \(M_s\cap T_s\) に残る|成立|
|有限停止|carry の5場合が端点 \(r+t=u\), \(t=0\) を含む。\(j>\lfloor(u-2)/2\rfloor\) では第一座標0、周期 \(p=u/\gcd(m,u)\) ごとの第二座標増大で後続が冗長となる|成立|
|\(P_C\le W\)|最短語の点を支配する点は、端点を除けばより短い同剰余内部語を与える。極小点 antichain の左右の個数が \(L_r+K_r+1\) 以下|成立|
|actual socle|\(M_s/(M_s\cap T_s)\hookrightarrow E/T_s\) が \(E\)-線形なので両変数 annihilator にも単射。\(E/T_s\) の Artin 性は不要|成立|
|\(T_s\) の角の計数|純 \(v\) 冪があるので第一座標最小0。極小点が \(z_s+1\) 個なら隣接角はちょうど \(z_s\) 個。最後の第二座標 \(\kappa_s>0\) を0と仮定していない|成立|
|carry の相殺|\(r\mapsto(r+m)\bmod u\) は \(\gcd(m,u)\) に関わらず置換。\(\sum c_r=m\), \(\sum\kappa_s\ge m\) を明示して \(R\le W-u\) に結ぶ|成立|
|height の向き|全競合生成元の第一座標が \(\max(H_x-2,0)\) 以下。\(H_x\) は元の core に固定し、反射した量を代入しない|成立|
|端点 Euler|\(G\) は \(E\)-有限生成、\(v^m=0\) なので rank 0。必要なのは有限長の端点 homology であり、\(G\) 自体の有限 \(k\)-次元性を仮定していない|成立|
|\(Q_C\to Q_G\) の補償|実核の長さが \(P_C-P_G\)。Tor 長完全列と内部鎖群上界から出る項が、二重複体の \(P_G\) と正確に相殺する|成立|
|全行と上端|第0行を \(\operatorname{Tor}_0=k\) として扱い、\(q+2\) 行は二項係数の消滅により \(R\)、その上は source の Koszul 複体消滅。target 行を誤って消していない|成立|

とくに V02 E13–E14 の **実核 \(N_s\) の exact corner 計算**を外しても、
実核の同定自体は E-7 に残る。以後は \(E/T_s\) への単射と \(T_s\) の角上界だけで閉じる。
N4 の本証明も exact \(N_s\) 角を利用せず、\(R\le\widehat R\) だけを使う。
したがってこれは必要説明を付録へ隠す操作ではなく、不要な強い計算の実際の除去である。

## Artin 評価と q=2 の検査

親子計数で \(D_n\setminus B_{n+1}\) が初期イデアルの次数 \(n+1\) の極小生成元を数える。
子の重み和1と親の上界 \((n+q)/(n+1)\) は有限集合上の有理数計数であり、体内除法を使わない。
\(h_1=q\) を分離した telescoping により E-14 の定数
\((q+1)(q+2)/6\)、\((q+1)^2/4\)、\(q=5\) の14が正確に得られる。

E-15 の小行列では、係数次数0の各 wedge \(I\) に対し
\((y_{\min I}, I\setminus\{\min I\})\) の行を選ぶ。
同じ行を持つ別列はなく、\(A_1\) の変数像は独立なので対角成分 \(\pm1\) の minor がある。
従って \(\operatorname{rank}d_i\ge\binom qi\) と
\(\operatorname{rank}d_{i+1}\ge\binom q{i+1}\) は任意体で有効。
E-GEN の加法形は E-TOR と Pascal 恒等式から得られ、Nat 飽和減算の正当性も確保する。

q=2 については、固定次数 \(n\) の内部語の offset が
\(na+j(b-a)\) と互いに相異なることに加え、E-RESOURCES で証明した
「\(Q_C\) は core 単項式基底の部分集合を基底に持つ」を使っている。
この二点により、生きた内部語の像に線形関係がなく、核が単項式 ideal となる。
一般 q の \(Q_C\) を単項式商とみなす誤りはない。
socle 計数も各固定乗法の非零像の相異性から成立し、
Betti 列 \((1,\sigma_C+1,\sigma_C)\) は top Koszul と rank-zero Euler で導ける。

## 必須修正と留保

このレビューからの必須修正はない。
E-10 の \(z_s\le A+B-\kappa_s\) は本文の「左右の個数」を、必要なら
「\((A,B)\) を割る極小点 \((A_j,B_j)\) を取り、
\(j\le A_j\)、\(z_s-j\le B_j-\kappa_s\) を加える」と一行展開できる。
これは監査の便宜のための任意の補足であり、未証明の数学的義務ではない。

一般的な Koszul/Tor、有限生成次数付き加群の最小解消、Gröbner 除法は通常の基礎代数として使用する。
その一般定理の再証明と、対象 commit の Lean 全依存の独立再コンパイルは本レビューの範囲外である。
