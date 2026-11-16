# R39：十一生成元の無条件全域証明

## 定理

Γを真正な最小十一生成元数値半群、kを任意体とする。最小・最大生成元の間の全整数を
加えた区間完備化を Γ̃ とする。このとき接錐について、全 i≥0 で

\[
\beta_i(G_\Gamma)\le\beta_i(G_{\widetilde\Gamma}).
\]

左右の Betti 数はそれぞれの**実際の最小表示環**上で取る。Cohen–Macaulay 性、
標数、重複度、生成元の大きさには追加条件を課さない。
以下は全パラメータを分割して証明書へ接続する論証である。

## 1. 正規化と完備化

最小生成元を m、生成元差の最大公約数を d とし、

\[
\Gamma=\langle m,m+da_1,\ldots,m+da_9,m+du\rangle,
\quad 0<a_1<\cdots<a_9<u,
\]

と書く。数値半群性から gcd(m,d)=1、正規化から gcd(a₁,…,a₉,u)=1、また u≥10、m≥11。
完備化の実効幅は V=min(du,m−1)。その表示環は V+1 変数であり、十一変数とは限らない。

領域 I を m>u、領域 II を m≤u とする。この二つは排反で全 source を覆う。
領域 II では du≥m だから Γ̃=⟨m,m+1,…,2m−1⟩、正次数の容量は i C(m,i+1)。

## 2. 領域 I：幅側

|正規化幅|担当する証明|有限部分の完全性|
|---|---|---|
|u=10|算術列 source の正確な Betti 公式|唯一の core。V=10 の境界も別扱いして証明|
|11≤u≤13|`lanes/core/R39_NINE_INTERIOR_CORE_PROOF.md`|10+55+220=285 個すべて|
|u≥14|`lanes/core/R39_UNIVERSAL_WIDTH_TAIL.md` W1|全 e≥8 の記号的定理を e=11 に適用|

有限 core は端点を除く九変数の Artin 商 Q を整数単項式基底で構成する。
実接錐の端点商 Q_G への核を K とすれば、核の長さを残した Tor 長完全列から

\[
\beta_i(G)\le b_i(Q)+P_C\binom9{i-1}
                         +\widehat R\binom{10}{i-1}
\]

を得る。ここで P_C=dim Q、R̂ は実接錐の端点共通 socle の一様上界。
この不等式の m,d に依存しない導出は原証明第3–4節に全て記載した。

全286 core のうち1個が算術列、105個が共通上界、180個が個別 unit-minor 上界で閉じる。
後者の92反射代表について31,416 strand、282,744境界の原整数小行列を収録した。
独立 consumer は Pareto 極小点から基底を再構成し、全境界、d²=0、各方向の socle、
全 source 行比較を検査する。反射した core の方向依存量は各々再計算する。

全ての rank 下界は元の整数行列の determinant ±1 の小行列による。
非単位残差68個を容量上界の計算で切り捨てず保持しているため、任意体で成立する。
別検査では67個の追加 Smith 因子2と、追加の原 unimodular minor を持つ1個を分類したが、
この分類を仮定して主比較を支払ってはいない。

u≥14 は W1 の閾値 11+ceil√8=14 そのもの。
有限幅からの数値的な外挿は行わない。これで領域 I が全て閉じる。

## 3. 領域 II：重複度側

|重複度・first-hit|担当する証明|
|---|---|
|m=11|最大埋め込み次元の標準定理|
|m=12|`input/R38/input/R37/R37_UNIVERSAL_DEFECT_ONE.md`|
|13≤m≤65|完全な十一変数 Hilbert–lex 宇宙と残余構造定理|
|m≥66|`lanes/lex/R39_UNIVERSAL_LOGARITHMIC_TAIL.md` の有理数 anchor と差分証明|

有限 Hilbert 宇宙は h₀=1,h₁=11、first-hit ρ≤m−1、pre-hit 1≤h_d<m、
hit 後 h_d=m、全 Macaulay 遷移を含む。pre-hit の下降を一般には除かない。
実 x 乗法が hit 後同型になることから実 Tor cutoff j≤ρ+i を得て、
同じ Hilbert 関数の lex ideal の degree≤ρ+1 の極小生成元を EK 公式で数える。
lex 自体の regularity を実 source の cutoff で切ったわけではない。

前向き原単項式 producer、後向き二項展開 producer、異なる二つの独立 consumer が
全4,032 node、135,792 edge、1,961 exact profile、21,571行比較で一致する。
全 path 数、極値証人、全行の得点も一致し、単に最終 hash だけを比べてはいない。

raw lex で容量を超えるのは m=13 の五つの scalar 比較だけである。

|ρ|行|raw lex|容量|実 source の支払い|
|---:|---:|---:|---:|---|
|10|1|79|78|以下の単一 Hilbert 残余に P01 を適用|
|11|1|80|78|R38-D2 の全 Tor 定理：第1行57|
|11|2|575|572|同じ定理：第2行350|
|12|1|81|78|同じ定理：第1行57|
|12|2|584|572|同じ定理：第2行350|

m−e=2 では D’Anna–Di Marca–Micale, Corollary 2.11 により Hilbert 関数が非減少。
実 Apéry 集合には0と十個の非重複度最小生成元を除いて二個しか残らず、下降に必要な
order2 の三個を持てないからである。この既知定理の原文は `STANDARD_REFERENCES.md` を参照。

ρ=10 の非減少かつ Macaulay admissible な列は八つ。
第1行の lex 上界が78を超える列は

\[
H_*=(1,11,12,12,12,12,12,12,12,12,13,13,\ldots)
\]

の一つだけである。`proofs/R39_PLATEAU_ONE_LADDER.md` はこの形を一般 m に拡張して扱い、
実 torsion が一つの二変数 ladder であることと実 connecting rank の整数単位小行列から

\[
\beta_i(G)\le i\binom{m-2}{i+1}+\binom{m-3}{i-1}
\]

を証明する。m=13 では β₁≤56≤78。この56という値は H_* に対する上界である。
他の七列を含めた ρ=10 profile 全体の、当該証明書での保証上界は78。
この区別は agreement checker にも保持してある。

したがって13≤m≤65の全列・全行が閉じる。
m≥66 では first-hit を保持した有理数 envelope U₁₁(m) と容量 C(m,2) の差が
m=66 で正、一次差分が正、二次差分 1−10/m が正となる。
同一 lex 極小生成元集合の比較から全行へ移るので、実 β₁の改善を機械的に他行へ
掛け算する誤りもない。これで領域 II が閉じる。

## 4. 全体・全次数への結論

i=0 は双方1。1≤i≤11 は上の比較、i>11 は十一変数の最小表示上で source 側が零。
全整数小行列、全記号的 Tor 論証、任意標数の BHP 定理により体の制限はない。
有限体について必要なら k→k(t) と体を拡大し、Hilbert 関数と graded Betti 数の不変性を使う。
よって主定理が成立する。

この証明は生成元追加の Betti 単調性、任意商での Betti 単調性、一般 torsion の平方零性を
仮定していない。最終8モードの実行事実は、凍結したこの証明とは別の外付け receipt に記録する。
