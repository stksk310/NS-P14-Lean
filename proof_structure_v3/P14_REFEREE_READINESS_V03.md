# P14 証明構造 V03：査読準備と未認証範囲

2026年11月9日。[新骨子](P14_PROOF_SKELETON_V03_JA.md)、[依存関係表](P14_DEPENDENCY_MAP_V03.md)、[全17節の置換台帳](P14_PROOF_REPLACEMENT_LEDGER_V03.md) のための読み順・監査境界を記す。ここでいう「レビュー済み」は保存された内部の独立担当レビューの範囲を指す。外部の公刊査読、第三者による全証明の再構成、Lean kernel による形式認証とは区別する。

## 1. 優先順位付きの査読経路

| 優先 | 難所と骨子の位置 | 査読者が確認する内容 | 現時点の根拠と残る作業 |
|---|---|---|---|
| P0 | actual source の固定：Part I・II・IV | ordinary の \(Q\) は numerical Apéry quotient、narrow の \(C\to G\) は元の source への写像であること。actual target の最小生成系と物理幅を確認する | V02 と個別監査に導出がある。外部読者は source の定義から写像・核を再構成し、抽象 profile や仮想正規化半群との取り違えがないことを全経路で確認する |
| P0 | A：jump strata → Tor の望遠和：Part II | 全体の \(T,N\) を同型視せず、同 jump のみ比較する。塔の完全列・Tor 劣加法性・\(d_2\)-rank の三段鎖を追う | `CORE_READABILITY_AUDIT.md` が独立導出を記録。橋の全記号と端の添字を骨子から原証明へ照合する |
| P0 | B：relative rank → actual ordinary target：Part II | 第0 homology の補正、target 差の係数、\(R_j\) が全行の十分条件であること、top rank を追う | 同 core 監査が補助式を提示。spectral sequence の退化を使わず、後続微分が次元を減らすことを確認する |
| P0 | C：actual endpoint kernel と carry：Part IV | 全長競合、\(N_s=M_s\cap T_s\)、\(\sum c_r=m\)、\(\sum\kappa_s\ge m\)、\(R\le W-u\)、核長補償を追う | `LATER_READABILITY_AUDIT.md` が中間計算を再構成。外部独立確認では端点模型から actual \(G\) までを切らずに読む |
| P0 | D：幅4・全 multiplicity：Part V | 自由列・制限列の網羅、\(K',L'\) の非負条件、正確な閾値、残る標準単項式の独立性から \(\operatorname{in}I_G=J\) を得る | V02 §14.6、N4 置換レビュー、後半可読性監査を保持。四つの剰余は全 \(m\) の記号計算でありサンプルではない |
| P1 | harmonic Koszul と同一資源列：Part II | 初項化の境界 rank、単位小行列、単一次数生成、区間計数、同じ cut に由来するすべての cap を追う | core 監査の対象。異なる cut の資源を混ぜないこと、有理重みが体内の除法ではないことを確認する |
| P1 | Apéry–Sidon＋5行 scalar：Part III | 最大二次層の剰余差単射、\(r\ge3\) の制限、固定 cutoff の恒等式、三つの実現不能な角を追う | ordinary 置換・独立 Sidon・接続レビューがある。共通代数の正当性はこれら単独では再監査されていない |
| P1 | N4 の紙上置換：Part V | Kneser 距離和、Savchev–Chen の正確な適用、三関係からの禁制 downset、\(u\ge9\)、幅5–8、幅3–4を追う | N4 置換レビューが新第一行を監査。共通端点補題と保持された高次行を前提とするレビューである |
| P1 | 五生成元以上の全幅領域：Part V | 各分岐の第一行と高次行、dense 幅の差、最小幅・小境界、target の非負補正を追う | V02 の保存済み全域監査と後半限定監査を参照。後半限定監査はこの領域全体を新たに査読し直したものではない |
| P1 | 大 rank scalar と全域合成：Part III・VI | 旧 scalar の rank 9 行・rank 10 以上、\(w\le m-2\) と \(w\ge m-1\)、\(e\le3\)、全行・任意体を追う | V02 の保持部分に依存。有限診断だけを無限範囲の根拠にしない。外部読者は再配置後の接続を一巡して確認する |
| P2 | 公刊入力と形式化境界：Part I・VI | 公刊定理の正確な statement・仮定・係数体・添字、形式化されていない依存を照合する | 本 run は新しい文献探索・原典の全面再査読を行わない。原典の定理と適用の外部確認および Lean 接続は残る |

P0 は「既知の反例がある」という意味ではなく、正しい接続を読者が独立に追うために最初に確認すべき箇所を示す。保存済み限定監査は対象範囲で結論を妨げる欠落を見つけなかったと記すが、これは全定理の外部査読済みという判断ではない。

## 2. A–D：省略しない橋の式

以下は骨子と完全証明の突合せに使う検査点であり、全補題の証明をこの一覧だけで代替するものではない。局所記号は各 Part の定義に従う。

### A. 同 jump の比較と三段の Tor 鎖

\(P=k[E]\)、\(B=A/X_2\)、\(L_j=c_j^P(B)\)。\(1\le j\le r\) とし、\(T\) の逆向き filtration の同 jump 成分を \(K_s\) と比較し、\(X_{\nu+1}=0\) を使う。

\[
\begin{aligned}
c_j(G)&\le L_j+c_j^P(X_2)+c_{j-1}^P(T),\\
c_{j-1}^P(T)&\le\sum_{s=2}^{\nu}c_{j-1}^P(K_s),\\
c_{j-1}^P(K_s)&\le c_{j-1}^P(M_s)+c_j^P(X_{s+1}).
\end{aligned}
\]

\(j=1\) では \(c_0^P(M_s)=\mu_P(M_s)\)。実際のスペクトル系列の rank を消す前の式は

\[
c_j(G)=c_j^P(A)+c_{j-1}^P(T)-\rho_{j+1}.
\]

完全列 \(0\to K\to M\to L\to0\) では

\[
c_j(K)=c_j(M)+c_{j+1}(L)
-\bigl(b_{j+1}(L)-d_{j+1}\bigr).
\]

最後の括弧は像の次元で非負。省くのは非負の減算補正であり、すべてを「connecting rank 自体」と呼ばない。\(T\) と \(N\) 全体の加群同型も、\(d_2=0\) も必要としない。

### B. 第0 homology 補正と target 差

\(R_0=k[x,E]\)、\(f=e-r-1\)、\(C(z)=\sum_{j=1}^r c_j(G)z^j\) と局所的に書く。\(\mathcal B_G^{R_0}=(1+z)((f+1)+C(z))\) とすると、正確な第0行を分離した評価は

\[
\mathcal B_G(z)\preceq T_{f+1}(z)
+(1+z)^f\bigl(\mathcal B_G^{R_0}(z)-(f+1)\bigr).
\]

\(T_{f+2}-T_{f+1}=(f+1)z(1+z)^f\) から V02 (8.1) が得られる。次に \(q=e-r\)、\(N_0=\delta+r-1=m-q-1\) と書けば

\[
\begin{aligned}
T_m-T_{q+1}
&=(1+z)^q\sum_{a=0}^{N_0-1}(q+1+a)z(1+z)^a\\
&=(1+z)^q\sum_{j=1}^{N_0}
\left[(q+j)\binom{N_0}j+j\binom{N_0}{j+1}\right]z^j.
\end{aligned}
\]

角括弧が \(R_j\)。\(1\le j\le r\) の \(c_j(G)\le R_j\) が十分で、\(j>r\) の target 係数は非負の余剰になる。範囲外の二項係数を0と読む。商の Betti 単調性は用いない。

### C. carry の相殺と actual kernel の補償

\(s_r=(r+m)\bmod u\)、\(c_r=(r+m-s_r)/u\)。最短点 \((L_r,K_r)\) の一段競合点を \((A_r,B_r)\) とすると \(A_r\le L_r\)、\(B_r=K_r+c_r\) であり、剰余の置換から \(\sum_r c_r=m\)。

\[
\begin{aligned}
\sum_s z_s
&\le\sum_r(A_r+B_r-\kappa_{s_r})\\
&\le\sum_r(L_r+K_r)+\underbrace{\sum_r c_r}_{m}
-\underbrace{\sum_s\kappa_s}_{\ge m}\\
&\le\sum_r(\ell_r-\epsilon_r)=W-u.
\end{aligned}
\]

socle の単射から \(R\le\sum_s z_s\)。別の height 評価と合わせて \(R\le\min\{W-u,u\max(H_x-2,0)\}\) を得る。ここで actual 核は \(N_s=M_s\cap T_s\) であり、\(T_s\) と同一視しない。

さらに \(K=\ker(Q_C\to Q_G)\) の長さ \(P_C-P_G\) を保持して

\[
\begin{aligned}
b_i^T(Q_G)&\le b_i^T(Q_C)+(P_C-P_G)\binom q{i-1},\\
\dim H_\bullet(x,v;G)&=(P_G,P_G+R,R),\\
\beta_i(G)&\le b_i^T(Q_C)+P_C\binom q{i-1}
+R\binom{q+1}{i-1}.
\end{aligned}
\]

\(P_C=P_G\) や、core から actual 商への Betti 単調性は仮定しない。

### D. 幅4の競合の必要十分条件

\(d=1,u=4,(a,b)=(1,3),m\ge6\)。標準列基点の次数・offset を \((c,n)\) とし、短い語を \(x^Lv^Kb\) とする。長さ超過 \(j\ge1\) に対して

\[
\begin{gathered}
r_j=(n-jm)\bmod4,\qquad
\kappa_j=\lceil(jm-n)/4\rceil,\\
\Delta_j=\lambda(r_j)-c-\kappa_j-j,\qquad
K'=K-\kappa_j,\quad L'=L-\Delta_j.
\end{gathered}
\]

offset と長さの等式から、この自由 anchor による競合の条件はちょうど \(K\ge\kappa_j,L\ge\Delta_j\)。

\[
4\Delta_j=(4\lambda(r_j)-r_j)-(4c-n)-j(m+4)
\le6-(m+4)<0.
\]

制限 anchor \(z^2\) は \(K\ge\kappa_j+1\) を要し、自由 anchor が既に覆う。\(\kappa_j\) は \(j\) について非減少なので、\(j=1\) が正確な閾値となる。消える標準単項式と、生存し同次数で相異なる実数値指数を持つ標準単項式を分け、後者の線形独立性から

\[
\operatorname{in}(I_G)=J_0+(bv^{\theta_n}),\qquad
J_0=(y^3,yz,xz^2,z^3),\quad
\theta_n=\max\{\lceil(m-n)/4\rceil,0\}
\]

の等号を確認する。その後に停止除算から \(\mu(I_G)\le\mu(J)\) を導く。単に生成元数を数例で比較した議論ではない。

## 3. その他の重要な式と境界

| 箇所 | 必ず追う式・条件 | 誤読を防ぐ理由 |
|---|---|---|
| 同一資源列 | \(H_0=\delta\)、\(H_t\ge0\)、\(\sum H_t\le\delta\mathcal V\)、\(H_t\le M\)、\(H_1\le M-a_r\) | 異なる cut の都合のよい cap を混ぜることを防ぐ |
| actual Apéry–Sidon | \(q_2=\binom e2\Rightarrow m\ge e(e-1)+1\Rightarrow\delta\ge(e-1)^2\) | 抽象 Artin 商の次元だけから multiplicity を制約しない |
| actual cut の範囲 | \(r=e-1\) **かつ \(r\ge3\)** なら最大二次層。\(r=2\) は直接評価 | 強制的な \(\max(2,p(q_2))\) の例外を守る |
| 新 scalar | \(G(r+1+s,a_r+t)=g+sA+tb+(1-\alpha)(\binom t2+st)\) と5行表 | 無限範囲は恒等式と符号で閉じる。有限試算からの外挿ではない |
| 三つの角 | \((r,e,\delta)=(6,7,21),(7,8,28),(8,9,36)\) | 負の基点を削除する actual-source 理由を明示する |
| 大 rank | 旧 §11 の \(r=9\) 行、\(r\ge10\) の固定 barrier・差分の符号 | 旧小 rank anchor を退けても大 rank の証明は残る |
| N4 の一括計数 | \(P_C\le2u-h-2+\binom h2\)、\(\sigma_C\le\min(h+1,k)\)、\(h=\lfloor u/2\rfloor\)、\(k=u-(b-a)\) | 禁制長方形と antichain を使う上界であり exact core 表の引用ではない |
| N4 高次行 | \((\beta_2,\beta_3,\beta_4)\le(2P_C+\sigma_C+3R,P_C+3R,R)\) と旧 §14.4 の target 比較 | 新第一行だけで全行を閉じたとしない |
| 幅4四剰余 | \(m>6\) で \(\mu(J)=(6,8,8,6)\)、\(F_1(m,4)=(7,10,9,8)\)。\(m=6\) は \(6<9\) | 四剰余は全 \(m\) の式。境界 \(m=6\) は別に扱う |
| dense 幅 | \(\mathscr D_i=i[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}]-(q+1+2t)\binom q{i-1}-R\binom{q+1}{i-1}-K\binom{q-1}{i-1}\) | target 第一項のみの支払いと、\(t=2,3\)、\(4\le t\le q\) の分岐を見える形にする |
| 合成 | \(w\le m-2\) と \(w\ge m-1\)。ordinary は \(r=2,3\)、\(4\le r\le8\)、\(r\ge9\) | 整数幅の境界と cut rank の全域を落とさない |

任意体性は各体上の Koszul 行列・整数座標・同標数の体拡大で扱う。異なる標数で actual Betti 数が等しいとは主張しない。第0行は双方1、ordinary の top relative rank、narrow の source top 行を含み、source の表示変数数を超える行は0である。

## 4. 保存された監査の範囲

| 保存資料 | 実際に監査した範囲 | この記録だけでは保証しないもの |
|---|---|---|
| [CORE_READABILITY_AUDIT.md](../auditability_search/CORE_READABILITY_AUDIT.md) | V02 §§2–10 の局所接続。strata、harmonic rank、A・B、scalar への全 rank 還元の中間式 | 公刊原典の全面再監査、§11以降、全定理の外部査読、Lean 認証 |
| [LATER_READABILITY_AUDIT.md](../auditability_search/LATER_READABILITY_AUDIT.md) | V02 §§11–17 と N4 置換稿の限定点検。C・D、dense 幅、依存版の相違と記号 | 後半全補題の新たな独立査読、既存資料を越える定理探索、形式認証 |
| [SIDON_INDEPENDENT_AUDIT.md](../auditability_search/SIDON_INDEPENDENT_AUDIT.md) | actual numerical Apéry quotient、差の単射、任意標数、三角の排除、\(r=2\) 例外 | ordinary 共通代数全体。末尾の任意的な強化 \(\ell\le e-2\) は主証明に追加しない |
| [ORDINARY_REDUCTION_REFEREE.md](../auditability_search/ORDINARY_REDUCTION_REFEREE.md) | 新5行表・(SO4)・符号・V02 基礎への接続。\(r\ge3\) の修正を確認 | 共通基礎全体を一から再監査したこと、N4 の正当性 |
| [ZERO_CERTIFICATE_REFEREE.md](../n4_further_reduction/ZERO_CERTIFICATE_REFEREE.md) | N4 新第一行、幅6–8の網羅、幅4全 \(m\) の保持箇所と転記 | 端点基礎・公刊入力の全面再証明、ordinary、全体の Lean 認証 |
| [NAVI_CROSS_REVIEW_JA.md](../navi_cross_review/NAVI_CROSS_REVIEW_JA.md)・[INCREMENT_REFEREE.md](../navi_cross_review/INCREMENT_REFEREE.md) | 独立代替の増分紙上証明、5基点、全行帰納、top 行、actual-to-formal の保持依存 | 主ルートへの採用、旧 first-hit の不要化、外部査読 |
| V02 の [統合監査](../proof_integrated_v2/INTEGRATION_AUDIT_JA.md)・[coverage](../proof_integrated_v2/GLOBAL_COVERAGE_MATRIX.md)・[最終数学レビュー](../proof_integrated_v2/audits/FINAL_MATHEMATICAL_REVIEW.md) | 旧依存版の構造・全域 coverage・保持された補題の監査記録 | 新しい V03 の依存が自動的に監査済みになること。旧「必須証書」表を V03 に持ち越す根拠 |

有限の回帰比較、ハッシュ照合、独立担当による紙上導出は、それぞれ別種の証拠である。「独立」という語も、このプロジェクト内の別実装・別担当と、外部数学者の独立査読を区別して使う。

## 5. 今回の限定確認と固定方針

今回の再構成では、新しい数学探索や大量の source 列挙を行わない。必要な算術 checker を一回ずつ実行した記録は次のとおりである。

| 今回の記録 | 観測した内容 | 証明上の役割・限界 |
|---|---|---|
| [SOURCE_RECEIPT.json](SOURCE_RECEIPT.json) | 四つの保存 package の manifest と計48 member の hash を固定し、旧資料の同一性を確認 | 旧稿・旧証書・旧コードの保存の確認。数学的正当性の代替ではない |
| [SMALL_SCALAR_RUN.json](audits/SMALL_SCALAR_RUN.json) | `FIVE_EXACT_SCALAR_ANCHORS_PAID`。新5行の有理定数、(SO4) の係数、角の隣の正余裕を確認 | 無限範囲の根拠は紙上の恒等式・符号と actual Apéry–Sidon 補題である |
| [LARGE_SCALAR_RUN.json](audits/LARGE_SCALAR_RUN.json) | barrier の全係数一致。保持する rank 9 の余裕 \(1/900\)、rank 10 anchor の余裕 \(181/8400\)。補助診断351件 | checker は旧 rank 4–8 の seed も再計算するが、それらは V03 の主依存に戻らない。有限診断は大 rank の普遍的証明の代替ではない |
| [WIDTH_ARITHMETIC_RUN.json](audits/WIDTH_ARITHMETIC_RUN.json) | `PASS_EXACT_COEFFICIENT_IDENTITIES`。Fraction 上の多項式全係数、疎幅の第一行、保持する高次恒等式、小幅容量を確認 | V02 §13 の算術補助。N4 共通端点・新第一行や A–D の数学的証明をこの出力だけで認証しない |

source は V02、N4 置換、ordinary 置換・可読性監査、Navi 別証明の四 package を追跡した。旧196組・83組の checker を、V03 主ルートのために再実行する必要はない。全17節の正確な見出しが台帳に一度ずつ現れることも照合した。

算術記録と別に、最終構造点検で確認・記録する対象は次のとおりである。

1. 主要 source と既存 manifest の同一性、全17節の新配置・保持・除外の照合。
2. 新5行表と (SO4) の有理数・係数・符号の再計算。
3. N4 紙上置換の依存、幅6–8の関係、保持する幅4と全高次行の照合。
4. A–D の中間式、同一 source・同一 cut・actual 核の保持の照合。
5. 主定理までの非循環な経路、全領域、任意体、全行・top 行の coverage。
6. 旧 §15、196組、Navi が主定理の必須前提へ戻っていないことの確認。

上表は実行を観測した算術記録であり、数学的な構造判定とは区別する。
[構造検査](audits/STRUCTURE_CHECK.json) は50頂点・128辺の非循環性、全頂点の到達性、
164個の明示的な出典式ラベルと4成果物の局所リンクを確認した。
[独立構造レビュー](audits/INDEPENDENT_ARCHITECTURE_REVIEW.md) はA–Dの橋、全域coverage、
任意体・全行、旧依存の除外を別担当が読解し、構造固定PASS、未解決指摘0と判定した。
構造化の過程で見つかった公刊入力のscope・依存記録・出典表示の5点は修正し、その範囲も記録した。
これらは補題の真偽を機械的に認証する検査でも、外部専門査読やLean認証でもない。
ここで必要確認を終え、同じ算術 checker の反復実行や無関係な大規模探索は追加しない。
既存 proof・code・certificate はすべて保存する。

## 6. まだ外部で独立検証すべき範囲

優先順位は、A・B の ordinary 共通代数、C の端点模型から actual kernel を経る移行、D の全 \(m\) の幅4証明、その後に五生成元以上の各幅領域・大 rank scalar・全域合成とする。新しい置換証明の局所レビューだけから、共通基礎まで改めて認証されたとは扱わない。

公刊入力については Green、必要箇所の BHP/EK、Kneser、算術列 Betti 公式と tangent cone 一致、三生成元比較、Savchev–Chen の statement と各適用条件を外部査読で照合する。外部定理への依存は「自前の証明がない欠落」と同一視しない一方、適用条件の確認は省略しない。

V03 は論理接続と必要中間式を固定する骨子である。将来の完全論文では、骨子から各保存完全証明へ往復せずに読めるよう、保持する補題の証明を統合して読む作業が残る。内部レビューが対象範囲で欠落を見つけなかったという結論と、完成論文の外部査読判定は別である。

## 7. Lean に残る仕事

この V03 再構成は Lean ファイル、toolchain、kernel 検証結果を追加しない。以下が形式化の実質的な作業として残る。

| 優先 | 形式化する内容 | 接続すべき構造 |
|---|---|---|
| L0 | numerical semigroup、真正な最小生成系、order、Apéry 座標、tangent cone と数値基底 | Part I・II・IV の actual source を同じ対象として構成する |
| L0 | graded module、Tor、Koszul、長完全列、filtration と bounded spectral sequence の次元不等式 | A・B と actual kernel 補償を形式的に接続する。退化を公理として仮定しない |
| L0 | 整数 core・競合座標・\(M_s\cap T_s\)・socle の単射と carry 和 | C の端点比較を元の actual \(G\) に戻す |
| L1 | Gröbner 除算、標準単項式の独立性、初期 ideal の等号、四剰余計算 | D の全 \(m\) の幅4証明を接続する |
| L1 | Sidon 差単射、5行の有理数表、固定 cutoff 恒等式、大 rank barrier、downset 計数 | 普遍的紙上証明と有限有理計算を区別して kernel 内で検証する |
| L1 | 公刊定理の形式 statement と使用箇所 | 既存の形式定理を使うか、新たに証明するか、明示した外部依存として管理する |
| L1 | field extension と Betti base change、各標数での行列 rank、全パラメータ分割 | 任意体・top 行・第0行・全生成元数を最終定理へ接続する |

文献の公刊定理を未証明 axiom として置き、主定理の型だけを作ることは完全な Lean 認証ではない。旧196組・83組の機械証書を主依存から外せても、上の構造と有理数恒等式を Lean で証明する必要は残る。内部監査済み、外部査読済み、Lean 形式認証済みの三つを混同しない。
