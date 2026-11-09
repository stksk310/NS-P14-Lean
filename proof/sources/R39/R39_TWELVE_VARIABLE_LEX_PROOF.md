# R39-L12：十二生成元の重複度側・全行閉鎖

## 1. 定理と全 multiplicity の分割

真正な最小十二生成元数値半群 `Γ` について、重複度 `m` が正規化最大 offset `u` 以下なら、
任意体、全ホモロジー次数で P14 が成立する。
実幅 `du≥m` なので completion は `⟨m,…,2m−1⟩` となり、比較する正次数容量は

\[
T_i(m)=i\binom m{i+1}.
\]

source の最小表示は十二変数、completion は `m` 変数である。

|重複度|適用する証明|
|---|---|
|`m=12`|最大埋め込み次元の一般定理|
|`m=13`|固定 R37 の欠損1・全行定理|
|`14≤m≤74`|本稿の完全な十二変数 Hilbert–lex 証明書|
|`m≥75`|R39 の普遍 lex tail の十二生成元 anchor|

後段は `lanes/lex/R39_UNIVERSAL_LOGARITHMIC_TAIL.md` の (LT6)–(LT10) により、
`D₁₂(74)<0<D₁₂(75)` と正の前進差分が全 `m≥75` を覆う。
この tail は第1行の実 Betti 数を機械的に他行へ掛け算したものではない。
同じ Hilbert 関数の truncated lex 第1行を EK の共通生成元集合を通して全行へ移す。

## 2. 有限宇宙と完全最適化

`lanes/lex/R39_ELEVEN_VARIABLE_LEX_PROOF.md` 第2–4節の一般証明を、変数数12で適用する。
実 source は

\[
h_0=1,\quad h_1=12,\quad1\le h_n<m\ (n<\rho),\quad
h_n=m\ (n\ge\rho),\quad2\le\rho\le m-1
\]

を満たし、実 `x=(t^m)*` の stabilization から
`β_{i,j}(G)=0` (`j>ρ+i`) が従う。
全 Macaulay 遷移を含めた graph で、lex ideal の極小生成元 `deg v≤ρ+1` の EK 重みを数える。
pre-hit の下降も一般の graph から除外しない。

`14≤m≤74` では `h₂≤C(13,2)=78` なので、全 `ρ=2,…,m−1` が到達可能。
全61 multiplicity、全 exact profile 数は

\[
\sum_{m=14}^{74}(m-2)=2562.
\]

四つの独立実装を、この十二変数の全範囲に対して実行した。

|実装|edge の構成|最適化・検査|
|---|---|---|
|forward producer|原単項式と全約数|前向き DP|
|backward producer|Macaulay 二項展開と block 計数|後向き DP|
|explicit consumer|direct stars-and-bars successor|全 graph と前向き DP 再計算|
|binomial consumer|初期変数支持の個数の差分|全 graph と前向き DP 再計算|

consumer は producer の関数を import しない。全意味内容・証人・path count を再構成し、
さらに実際に読んだ producer ファイルの SHA-256 を報告して replay の入力と結び付ける。

|対象|正確な個数|
|---|---:|
|multiplicity|61|
|union graph node|5,256|
|union graph edge|201,197|
|exact `(m,ρ)` profile|2,562|
|座標別極値証人|30,744|
|最終行比較|30,744|

意味内容 SHA-256：

`c13a1485694b9cf5da2ed3a7b4e23e883f3ba9dcc3e5415fcb1dc1755a5714ae`

## 3. Raw lex の不足は `m=14` に限る

`m=15,…,74` の全 profile・全十二行は raw lex で容量以下。
`m=14` の不足は次の14 scalar 比較である。

|`ρ`|不足する行と raw 上界|その行の容量|
|---:|---|---|
|8|第1行92|91|
|9|第1行93、第2行731|91、728|
|10|第1行94、第2行742|91、728|
|11|第1行95、第2行753、第3行3021|91、728、3003|
|12|第1行96、第2行764、第3行3076|91、728、3003|
|13|第1行97、第2行774、第3行3121|91、728、3003|

raw 上界が容量を超えることを、真正 source の反例と混同しない。

## 4. 欠損2に限った既知の Hilbert 制約

`m=14,e=12` は欠損2。
D’Anna–Di Marca–Micale, *On the Hilbert function of the tangent cone of a monomial curve*,
arXiv:1506.01797, Corollary 2.11 による非減少性を適用する。
Apéry 集合14元のうち0と非重複度生成元11個を除くと二つしかないため、下降に必要な
三つの order2 Apéry 元を持てない。

従って実 Hilbert 関数は

\[
H=(1,\underbrace{12,\ldots,12}_{a\ge1},
      \underbrace{13,\ldots,13}_{\rho-1-a},14,14,\ldots).
\]

全 `ρ=2,…,13` の候補78形のうち、Macaulay 成長条件を満たすのは71形。
`verify_twelve_monotone.py` はすべてを原単項式から検査する。
この制約は欠損2の実 source から証明されたものに限って用いる。

原文参照：<https://arxiv.org/pdf/1506.01797>、Corollary 2.11。
この既知の定理は R39 の新規成果とは数えない。

## 5. 実 source の三つの構造定理で全不足を除く

### 5.1 `ρ=8,9`

非減少な候補のうち raw 比較が失敗するのは `a=1` だけ。
この二つは `ρ>m/2`、`H₂,…,H_(ρ−1)=m−1` を満たすので、
`lanes/lex/R39_HIGH_FIRST_HIT_PLATEAU.md` により

\[
\beta_i(G)\le i\binom{12}{i+1}+\binom{11}{i-1}.          \tag{12P}
\]

特別 Hilbert 列の第1・第2行は `(67,451)` 以下。
その他の非減少 Hilbert 列を含めた全 profile の第1行上界は、`ρ=8` で91以下、
`ρ=9` でも91以下となる。特別 Hilbert 列の67を全 source の上界と取り違えない。

### 5.2 `ρ=10,11`

`t=m−ρ−1` はそれぞれ3,2であり、`ρ>m/2`。
`lanes/universal/R39_D2_SHORT_TAIL_ALL_TOR.md` の Theorem ST1 は、
この条件を持つすべての真正欠損2 source に対して

\[
\beta_i(G)\le i\binom{12}{i+1}+2\binom{11}{i-1}.         \tag{12S}
\]

を証明する。Hilbert plateau の仮定は不要。
実 source の短い tail と二つ以下の `k[x,y]`-ladder、実 connecting map の整数単位小行列が
根拠であり、元の torsion の平方零性を一般仮定していない。
第1・第2行の上界は `(68,462)` で、全高次行も同時に容量以下。

### 5.3 `ρ=12,13`

固定 R38-D2 の高 first-hit 全 Tor 定理が適用され、同じ (12S) が得られる。
これで第3行まで現れた raw の不足も一括して消える。

## 6. 完全性と scope

`certify_twelve_agreement.py` は全 graph の到達可能性、全 path count、全証人得点、
両 producer・両 consumer の完全一致と実 input hash、全 raw 不足集合、
71形の非減少宇宙と実構造定理への接続を検査する。
全2,562 profile・30,744 scalar 比較が通る。

`m=12,13` の既存一般定理、`m≥75` の新しい全 e lex tail と合わせて、
十二生成元の `m≤u` 全領域が閉じる。
数学的有限化と全パラメータ移行が証明の本体であり、実行 receipt 自体を数学的証明にはしない。

`m>u` の全域は core lane の独立な証明と統合する。
本稿は十三生成元や任意生成元数の全域を主張しない。

