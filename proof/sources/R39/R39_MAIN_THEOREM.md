# R39 主定理と厳格な判定

## 判定

**C. ELEVEN_GENERATOR_GLOBAL_CLOSED**。
同じrunでさらに **TWELVE_GENERATOR_GLOBAL_CLOSED** を得た。
任意生成元数の全域は **OPEN**。真正なP14反例は得ていない。

本書でいう閉鎖は、固定R38の原証明を継承し、新しい無限移行の証明、完全な有限整数証明書、
独立consumerを組み合わせた計算支援証明体系を意味する。外部学術査読やLean等の完全形式化を意味しない。
物理封印後の8モード実行の成否は、ZIP外の最終receiptだけに記録する。

## 主定理

Γを真正な最小e生成元数値半群、e∈{11,12}、kを任意の体とする。
最小生成元をm、最大生成元をg_eとし、区間完備化を

\[
\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle
\]

とする。実際の最小生成系による多項式環をそれぞれS_Γ、S_Γ̃とし、
G_Γ=gr_𝔪 k[[Γ]]と置く。このとき全i≥0で

\[
\boxed{\beta_i^{S_\Gamma}(G_\Gamma)
       \le\beta_i^{S_{\widetilde\Gamma}}(G_{\widetilde\Gamma}).}
\]

G_ΓのCohen–Macaulay性、標数、mや生成元の大きさに追加制限はない。
完備化は正規化刻みdだけを埋める操作ではなく、端点間の全整数を加える操作である。

## 全パラメータの分割

dを実生成元差の最大公約数とし、
Γ=〈m,m+da_1,…,m+da_(e−2),m+du〉と正規化する。
gcd(m,d)=1、u≥e−1、m≥e、実幅w=du、完備化の実効幅V=min(w,m−1)。

|領域|e=11|e=12|証明|
|---|---|---|---|
|m>u、有限幅|u=10,…,13、全286core|u=11,…,14、全364core|実sourceのkernel–Tor補償と原整数unit minor|
|m>u、無限幅|u≥14|u≥15|R39-W1の全e記号的定理|
|m≤u、最大埋込次元|m=11|m=12|既知の最大埋込次元公式|
|m≤u、欠損1|m=12|m=13|固定R37の一般D1定理|
|m≤u、有限重複度|13≤m≤65|14≤m≤74|全Macaulay graphと実source構造定理|
|m≤u、無限重複度|m≥66|m≥75|R39-LTの有理anchorと正の差分|

m>uとm≤uは排反で全sourceを覆う。後者ではw≥mなので完備化はordinaryであり、
正次数の容量はi C(m,i+1)。前者では実効幅Vを保ち、算術列接錐の正確な容量を使う。

## 有限部分と無限部分の接続

coreの候補集合は全ての内部offset組合せを含む。原整数境界のunit minorは全体でrank下界を与え、
非単位残差を捨てない。実端点商への核とsocleの補償が任意のm,dへの移行を支える。
反射による共有はArtin計算だけに限り、方向に依存するsource補償は各向きで計算する。

lex宇宙は全pre-hit Macaulay遷移を含み、一般には下降を除かない。
実x乗法の安定化から実Tor cutoffを証明し、同じHilbert関数のlex idealに次数別BHP上界を適用する。
四つの独立アルゴリズムが全graph、経路数、全極値証人、全行を照合する。
欠損2に限る既知のHilbert非減少性と、P01/P02/U08/R38-D2がraw lexの残余を支払う。

十一生成元の完全論証は `R39_ELEVEN_GENERATOR_PROOF.md`。
十二生成元の幅側は `lanes/core/R39_TEN_INTERIOR_CORE_PROOF.md`、
重複度側は `lanes/lex/twelve/R39_TWELVE_VARIABLE_LEX_PROOF.md`。
全領域の対応は `code/verify_global_coverage.py` が再計算済み証明書へ結び付ける。
この統合checkerは各無限補題の自動形式証明を代用するものではない。

## 全次数・任意体

i=0は双方1。1≤i≤eは上の全行比較、i>eはsource側が0。
整数のdeterminant±1、実Koszul長完全列、明示的T-module、任意標数のlex上界によって体の制限を除く。
必要な既知定理を無限体上で述べる場合はk→k(t)で体を拡大し、Hilbert関数とgraded Betti数の不変性を使う。

## この版の出自

以前に封印したR39は環境断により失われた。このZIPは回収した全文と新たな再構成を統合した別の成果物である。
二つのcore証明書、P03証明・checker・証明書、十一生成元主証明等には旧hashとの一致がある。
lexの全意味内容も旧hashを再現した。旧ZIPそのもののbyte一致は主張しない。
詳細は `R39_RECOVERY_PROVENANCE.md` と各laneの復旧記録を参照する。
