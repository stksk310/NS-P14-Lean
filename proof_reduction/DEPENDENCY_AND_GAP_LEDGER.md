# 依存と未認証部分の台帳

2026年11月9日。`VERIFIED` は、記した数学的仮定の下で原証明を読解・導出して確認したことを表す。Lean検証済みという意味ではない。有限診断だけを根拠に普遍命題へこの印を付けない。

## 主鎖の状態

| 命題 | 判定 | 根拠・残る条件 |
|---|---|---|
| 非Apéry部分 \(N\) のideal性 | VERIFIED | 生きた積で前駆元が存在する性質が保たれる。非x全変数に関するidealとして扱う。 |
| terminal–head対応 | VERIFIED | 死んだx矢印と非Apéry headの基底全単射。加群全体の同型は仮定しない。 |
| jump filtration・共通strata | VERIFIED | T側ではjump非減少、N側では非増加。等jump作用のみを同定し、一般線形cutへ制限する。 |
| jump上界・実際の塔 | VERIFIED | Apéry商の正則性上界、座標極小生成元、jump非増加から全jumpを制限。各truncationは実際の完全列。 |
| \(H_1=\delta-a+\ell\le m-1-a\) | VERIFIED | 同じ塔での厳密な座標計数。\(\ell\le e-1\)。 |
| \(L_\rho\le\delta+1\) とvolume | VERIFIED | 本文第3節の経路補題で初等的に再証明。Eliasへの依存を除去。 |
| residue occupancy | VERIFIED | 同剰余の寄与区間が互いに素。\(H_t\le m-1\) と総量を同時に使用。 |
| Green cut・有限体降下 | VERIFIED | 公刊Green次数2制限定理に依存。無限体へ純超越拡大し、同じ標数内で最終Betti数を戻す。 |
| 一般有限長加群の(H) | VERIFIED | 本文第6節の直接Koszul証明。一般加群も同shiftの初項基底と三角小行列で処理。任意体。 |
| Tor connecting rankの符号 | VERIFIED | \(b_i(M)=b_i(K)+b_i(L)-d_i-d_{i+1}\)、\(c_j(M)=c_j(K)+c_j(L)-d_{j+1}\)。 |
| x-first接続 | VERIFIED | 2行スペクトル系列の \(d_2\) だけが残り、\(c_j(G)=c_j(A)+c_{j-1}(T)-\rho_{j+1}\)。 |
| 2本・3本cut | VERIFIED | 本文第9節。旧 \(e\ge13\) のV下界を引き継がず、強いH1 capを使い直した。 |
| 4本以上・top rank | VERIFIED | 同じcutの全重みを一つの \(F_r\) で支払い、topも含む。 |
| e≥10 scalar | VERIFIED | 全actual \(r\ge4,\delta\ge\binom{r+1}2\)。調和数アンカー、r帰納、δ偶奇差分、正のe傾き。独立の別導出でも一致。 |
| 実ordinary target移行 | VERIFIED | 最小表示、平方零quotient、Koszul二重複体、明示R予算を使用。商のBetti単調性や退化は仮定しない。 |
| Wのe≥5拡張 | VERIFIED | [幅側証明](WIDTH_REDUCTION_PROOF.md)。端点移行と公刊算術列公式・Kneser・BHP/EKに依存。有限core campaign不要。 |
| 小ordinary残余 | VERIFIED | [小ordinary証明](SMALL_ORDINARY_PROOF.md)。actual有限化と全first-hit最大化を再証明。83組・665比較、5本の紙上tail。公刊BHP/EKに依存。 |
| 3生成元のnarrow | VERIFIED | 公刊Lan–Tu–Vu。理想のBetti比較を商のBettiへ1段ずらし、第0行1を補う。 |
| N4：物理的true narrowの4生成元 | CONDITIONAL | 下記。全祖先の独立認証は今回未完。 |
| P14の無条件完全認証 | NOT_YET_CHECKED | N4を残している。Lean形式化も未実施。 |

今回の重点査読で、FALSEと分類する主鎖命題や真正なP14反例は見つかっていない。これは全祖先の無条件完全認証を意味しない。

## 最後に残すN4の範囲

\[
 e=4,\qquad w=g_4-m\le m-2,
\]
のactual sourceについて、任意体・全Betti行でP14という境界である。\(d>1\) も含む。\(u<m\) だけを境界とすると、物理的ordinaryの旧wide枝まで祖先へ戻ってしまう。今回はactual targetの物理幅で分け、ordinaryの4生成元は新しいr2/r3補題で処理した。

原証明の主な所在は、最初のR01〜R57 handoffの `04_HISTORICAL_THEOREMS/R27_LITERAL_PROOFS.md` にあるR27-F01、primitive true narrowのR27-A01、nonprimitiveのR27-D01、必要な高次行のR26-A01、境界例外族のR24-N02。[N4出典表](N4_SOURCE_MAP.md) にmember名・行・ハッシュを示す。選択された新入力に含まれないものも、前ターンの完全handoffの保存objectから参照可能である。**資料の物理的不在とは判定していない。**

R25のgraph/TU型の中間定理は、4生成元の端点Koszul式で置換できる。実 \(Q_G=G/(x,v)G\)、\(P=\operatorname{length}Q_G\)、\(\sigma=\operatorname{soc}_{y,z}Q_G\)、\(R=(0:_G(x,v))\) とすると、2変数Artin商のBettiは \((1,\sigma+1,\sigma)\)。従って
\[
 \beta_1\le P+R+\sigma+1,\quad
 \beta_2\le2P+3R+\sigma,\quad
 \beta_3\le P+3R,\quad\beta_4\le R.
\]
これによりN4の必要依存からも、graph rankと全相殺の枝を外せる。しかし残る数値座標模型、primitive tail、例外族、nonprimitiveの全祖先まで独立認証を完了したとはしない。

一部の旧checkerのbyte復元と再実行は成功している。[N4部分再現記録](N4_PARTIAL_REPLAY.json) に、13,921 offset、4,824 actual例＋108 tail、16 Taylor証明書の範囲を記す。有限例と、既に証明された周期性・tailへの還元を区別する。この記録をN4全体の新しい完全証明にはしない。

## 公刊入力の範囲

- [Caviglia、Green制限定理の著者本文](https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BS4%5D.pdf)、§1、式(1.1)：無限体上、標数制限なし。今回は次数2のみ。原文を今回直接確認した。
- [Lan–Tu–Vu、Betti numbers of the tangent cones of monomial space curves](https://arxiv.org/html/2307.05589v1#S1)、Theorem 1.1：3生成元、任意体、実際のinterval completion。今回直接確認した。
- BHPの任意標数版とEK：幅側のlex telescope、小ordinaryのtruncated lex上界に使用。Peeva連続消去定理は新しい証明では使わない。
- Kneser：有限巡回群、合成数位数を含め、stabilizerつきの和集合下界。
- 算術列のBetti公式と接錐との一致：Gimenez–Sengupta–Srinivasan Theorem 4.1とHerzog–Stamate Proposition 2.5。半群環と接錐の一致を一般sourceへ拡張しない。

公刊定理を本runで全て再証明したという扱いにはしない。Leanでは正確な定理のライブラリ化・接続が必要である。

## 版と証拠

入力ZIP、旧本文、採用原文のSHA-256は [SOURCE_RECEIPT.json](SOURCE_RECEIPT.json)。新しい有限算術とコードの実行範囲は [verification.json](verification.json)。原資料のCLOSED/PASSラベルは数学的入力にせず、証明と式・計算範囲を確認した。
