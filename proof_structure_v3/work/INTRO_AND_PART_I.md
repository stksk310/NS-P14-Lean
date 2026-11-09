# P14 全域証明の骨子 V03

2026年11月9日。今後の全文執筆に先立つ、主証明の構成・statement・接続式の確定稿。
V02の全文改稿、論文の完成、Lean形式認証を意味しない。

**採用する主ルートは一つである。ordinary側を同じcutのApéry塔とscalarで閉じ、
狭幅側をactual核を保った端点移行で閉じる。**
ordinaryの残部はApéry–Sidonと5行の表、N4の第一行は紙上の一括評価と少数の場合分けを使う。
旧第15節と196組証書、ナヴィのlex増分ルートは主証明に重ねない。

## この骨子の読み方

以下の各補題IDは [完全依存表](P14_DEPENDENCY_MAP_V03.md) と
lemma_registry.json のIDに一致する。各項目には、何を証明するか、適用範囲、
核心、次の接続、完全証明の所在を示す。証明の要点だけでは復元しにくい四つの橋は、
この骨子でも途中式を表示する。完全証明を省略した箇所を「監査済み」というラベルで代用しない。

~~~mermaid
flowchart TD
  T["主定理：actual completionとの全Betti比較"]
  T --> S["e≤3：直接計算・公刊三生成元定理"]
  T --> O["ordinary：w≥m−1"]
  T --> W["狭幅：w≤m−2, e≥4"]
  O --> A["数値Apéry・同jump strata・一つのcutと塔"]
  A --> K["harmonic Koszul → Tor → actual target"]
  K --> L["r=2,3：直接評価"]
  K --> M["r=4..8：Sidon＋5行scalar"]
  K --> H["r≥9：大rank評価"]
  W --> E["有限端点座標・全競合・actual核・Tor補償"]
  E --> G["e≥5：edge/dense/sparse/e=5構造"]
  E --> N["e=4：紙上N4＋全高次行＋幅4"]
~~~

矢印は読者が結論から根拠へ追う方向である。機械可読なdepends_onも同じ向きとし、
循環がないことを別途確認する。

## Part I 主定理、実際の比較対象、公刊入力

### I.1 主張と量化範囲

\(\Gamma=\langle m=g_1<\cdots<g_e\rangle\) を真正な最小生成系を持つ数値半群、
\(k\) を任意の体とする。
\[
G_\Gamma=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]],\qquad
\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle.
\]
各環を、それぞれの最小生成系に対応する多項式環で表示してBetti数を取る。
主定理は
\[
\boxed{\beta_i(G_\Gamma;k)\le
       \beta_i(G_{\widetilde\Gamma};k)\qquad(i\ge0).}
\tag{V3-MAIN}
\]
同じ数の変数を無理に両辺へ加えて比較する主張ではない。
双方の第0行は1、sourceの \(i>e\) 行は0。
負の下添字・上添字を超える下添字の二項係数を0とする。

物理幅を \(w=g_e-m\) とする。\(e\ge2\) の場合だけ
\[
d=\gcd(g_2-m,\ldots,g_e-m),\qquad u=w/d
\]
を定める。\(e=1\) に空集合のgcdを適用しない。

### I.2 記号の局所範囲

| 領域 | 固定する記号 | 区別すべき量 |
|---|---|---|
|ordinary| \(\delta=m-e,\ M=m-1,\ \mathcal V=e+\delta/2-3/2\) | \(\mathcal V\) は資源係数で幅ではない |
|ordinary| \(r\) はcut本数、\(a=q_2\)、\(a_r=\binom{r+1}{2}\) | \(\delta\) を局所的に \(d\) と改名しない |
|ordinary| \(P=k[\lambda_1,\ldots,\lambda_r]\)、相対環 \(k[x,\lambda_1,\ldots,\lambda_r]\) | \(c_j\) は環を指定したTor交代和 |
|narrow| \(q=e-2,\ 0<a_1<\cdots<a_q<u,\ V_{\rm phys}=du\) | 実効target幅は \(\min(du,m-1)\) |
|narrow| \(Q_C=C/(x,v)C,\ Q_G=G/(x,v)G\) | endpoint変数 \(v\) とtarget幅を区別し、target幅は \(V_{\rm tar}\) とする |
|narrow| \(P_C=\dim Q_C,\ P_G=\dim Q_G,\ R=\dim(0:_G(x,v))\) | core商・actual商・actual socleを混同しない |
|幅4| \(m=4Q+\rho\) | 商 \(Q\) は内部変数数 \(q\) と区別する |

骨子中の引用式が旧記号を使うときは、その節の宣言を優先する。
論理的に別の量の同一視は行わない。

### I.3 Actual interval容量：I_TARGET

\(m\ge2\) とする。実効幅
\(V_{\rm tar}=\min(w,m-1)\) に対し、completionのatomは正確に
\(m,m+1,\ldots,m+V_{\rm tar}\)。
\[
D_{\rm tar}=V_{\rm tar}-((m-1)\bmod V_{\rm tar})
\in\{1,\ldots,V_{\rm tar}\}.
\]
算術列公式と接錐のBetti一致から、全 \(i\ge1\) で
\[
F_i(m,V_{\rm tar})
=i\binom{V_{\rm tar}}{i+1}+
\begin{cases}
(D_{\rm tar}+1-i)\binom{V_{\rm tar}}{i-1},&i\le D_{\rm tar},\\
(i-D_{\rm tar})\binom{V_{\rm tar}}i,&i>D_{\rm tar}.
\end{cases}
\tag{V3-TAR}
\]
\(i>V_{\rm tar}\) は0。剰余別最小容量
\[
F_i^{\min}(v)=i\binom v{i+1}
 +\min\left\{\binom v{i-1},\binom vi\right\}
\tag{V3-TMIN}
\]
は各行で \(v\) について非減少。
ordinaryでは \(V_{\rm tar}=m-1\) なので \(F_i=i\binom m{i+1}\)。
狭幅側はactual幅から \(F_i^{\min}(u)\) を引き出すだけで、
sourceやtargetを正規化した仮想半群に置き換えない。

**役割・接続。** ordinaryのtarget多項式、幅側の全行容量を一度だけ固定する。
完全証明は [V02 §1.3](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:83)。

### I.4 公刊入力と基礎代数の境界

| ID | 使用する正確な入力 | 主ルートでの使用先 |
|---|---|---|
|X_GREEN|Green、次数2の超平面制限。Caviglia §1 (1.1)に再掲|ordinary cut|
|X_BHP_EK|BHP任意標数版とEK公式。Juhnke-Kubitzke–Venturello §2.2 Lemmas2–3|幅側dense lexのみ。旧ordinary lexへの辺は外す|
|X_KNESER|DeVos Theorem1のKneser和集合定理。合成数位数を含む|幅側距離和・N4|
|X_AP_BETTI|Gimenez–Sengupta–Srinivasan Theorem4.1|actual targetとW_EDGEの算術列source|
|X_AP_CONE|Herzog–Stamate Proposition2.5|actual targetとW_EDGEの算術列sourceの接錐一致|
|X_LTV|Lan–Tu–Vu Theorem1.1|真正な三生成元の全域比較|
|X_SC|Savchev–Chen §4 Theorem8|N4混合標準語|

原典リンクと正確な適用説明は
[V02 §1.2](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:37)。
これらの定理を今回再証明したとはしない。

X_BASICはKoszul/Tor、Hilbert syzygy、rank Euler、有界spectral sequence、
同次Gröbner除法という通常の基礎代数である。
「任意商のBetti単調性」や「spectral sequenceの退化」は入力に含めない。

### I.5 任意体性：I_FIELD

一般一次形式を選ぶordinary cutの段階だけ、必要なら同標数の無限純超越拡大へ移る。
最小自由解消のflat base changeによりBetti数は元の体と等しく、最後に下降できる。
他の議論は各体上のKoszul複体、整数の単位minor、数値的な有理不等式で行う。
有理数の重みを評価に使うことは、基礎体内でその分母を割ることではない。
異なる標数のactual Betti数が等しいとは仮定しない。

**完全証明・接続。** V02 §4、§16。以下のO_CUTを正当化し、
狭幅側は各体上で直接進める。
