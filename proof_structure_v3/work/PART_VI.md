## Part VI 全域合成、検証境界、全文執筆への接続

### VI.1 小生成元数：I_BASE、I_THREE

\(e=1\) なら数値半群は \(\mathbb N\) でありsourceとcompletionが等しい。
\(e=2\) なら \(\Gamma=\langle m,n\rangle,\ m<n,\ \gcd(m,n)=1\)、
\[
G_\Gamma\simeq k[x,y]/(y^m),\qquad
(\beta_0,\beta_1,\ldots)=(1,1,0,\ldots).
\]
これは \(y^m-x^n\) の最低次数項から従う。
completionの定義理想は非零なので第一行は少なくとも1であり、比較が成立する。

\(e=3\) はX_LTVを用いる。理想から商への添字換算と第0行1を含める。
ordinaryのcut2による別の証明も存在するが、全域合成では三生成元をこの一箇所で処理する。

**完全証明。** V02 §1.2(5)、§16。ここに旧第15節への依存はない。

### VI.2 境界を含む全域coverage：I_NORMALIZE、I_PARTITION

以下 \(e\ge4\) とする。整数幅 \(w\) は次の二つのどちらかを満たす。

| 領域 | 接続する仮定 | 適用先 |
|---|---|---|
|\(w\ge m-1\)|actual completionはordinary。\(2\le r\le e-1\)|O_CLOSE|
|\(w\le m-2,\ e=4\)|\(q=2,\ m\ge du+2,\ 0<a<b<u\)、gcd条件|N_CLOSE|
|\(w\le m-2,\ e\ge5\)|\(q=e-2\ge3,\ q+1\le u<m,\ m\ge du+2\)、gcd条件|W_CLOSE|

正規化では
\(d=\gcd(g_2-m,\ldots,g_e-m)\) とし、offsetを \(d\) で割る。
sourceの値・生成元は変えない。
\(\gcd(m,d)=1\) と正規化offsetのgcd1は数値半群のgcd1から従う。
幅境界 \(w=m-1\) はordinaryに含むので、未処理の整数幅はない。

ordinaryでは次の三分岐が全cutを覆う。
\[
\begin{array}{c|c|c}
r&追加条件&閉鎖補題\\ \hline
2,3&各低cutのactual条件&O_{\rm LOW}\\
4,\ldots,8&e\ge r+1,\ \delta\ge a_r&O_{\rm SMALL}\\
r\ge9&e\ge r+1\ge10,\ \delta\ge a_r&O_{\rm LARGE}
\end{array}
\]
O_SMALLでは \(r=6,7,8\) の負の基点をactual Apéry–Sidonで排除する。
\(r=2\) へ最大二次層の推論を適用しない。
\(\delta=0\) は空の塔としてO_LOWに含まれる。

狭幅では、W_CLOSEが最小幅・一欠落幅・dense・sparse・五生成元の端を処理し、
N_CLOSEが全正規化幅 \(u\ge3\)、全 \(d\ge1,m\ge du+2\) を処理する。
N4の第一行を新しくした後も、N_HIGHとN_WIDTH4を消さない。

### VI.3 全行・任意体の結論：I_MAIN

I_BASEとI_THREEにより \(e\le3\) が閉じる。
\(e\ge4\) ではVI.2の排他的な幅分割を行う。
ordinaryはO_CLOSE、狭幅の四生成元はN_CLOSE、五生成元以上はW_CLOSEで全行が閉じる。
O_TARGETおよびE_TRANSFERは後続spectral pageの次元減少を使うだけで退化を仮定せず、
actual targetの容量はI_TARGETに固定されている。
従って全source・全 \(i\ge0\) の(V3-MAIN)へ接続する。

sourceの上端 \(i=e\) は各閉鎖補題の範囲に含まれる。
\(i>e\) はHilbert syzygyによりsourceが0、第0行は双方1。
N4では特に \(i=4\) をN_HIGHで処理する。
最小幅でtargetの上端が低い場合も、W_EDGE又はN4の同一target/幅4処理が対応する。

任意体性はI_FIELDと、各補題の標数に依存しない証明を合わせる。
この段階で新たな有限半群の計算や、異なる標数のrank比較を追加する必要はない。

### VI.4 主証明に残る算術、外した歴史的依存

主ルートには、小さい有理数表、barrier恒等式、多項式係数の符号、
幅6–8の明示的な代数の場合分け、幅4の四剰余が残る。
それらは各数学的statementと証明の一部である。

旧196組・旧83組・665行比較・旧5tailの列挙証書は、主定理の必須依存から外れる。
コードが不要になったという意味ではなく、残すコードの役割は
定義式からの正確な算術検算と任意の回帰確認である。
有限回帰の成功から無限範囲を結論しない。

ナヴィの \(\Delta B_1\le m-2\) は独立した別証明として
[クロスレビュー](/workspace/NS-P14-Lean/navi_cross_review/NAVI_CROSS_REVIEW_JA.md) に保存する。
それはfirst-hit/truncated lexを保持するため、この主DAGには辺を加えない。

### VI.5 今回固定するものと、次の全文執筆で行うもの

今回固定するのは、各補題の量化範囲、依存、完全証明の所在、四つの橋の途中式、
全域coverage、および内部監査と形式認証の区別である。
単一骨子が完成しても、各公刊定理や共通代数をLean kernelが確認したことにはならない。

次の全文執筆では、この順序で完全証明を移し、局所記号を統一し、
旧節番号から新しい補題番号への参照を一度だけ更新する。
旧稿を切り貼りして不要な旧証書の必須参照を残すことは避ける。
監査課題と形式化の範囲は
[査読準備表](P14_REFEREE_READINESS_V03.md)、
移動・保持・置換は
[置換台帳](P14_PROOF_REPLACEMENT_LEDGER_V03.md) に記録する。
