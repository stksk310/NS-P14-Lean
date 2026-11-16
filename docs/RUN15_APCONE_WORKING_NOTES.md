# Run15 APCone checkpoint後も継続

基準3e82d46、5新規数学module、一般APConeBettiGoalそのままのaudit、全92検証PASS、全5622/新規52宣言。通常/explicit型・公理・旧原本不変を保存。一般APBettiGoalのみ未完。過去の原本を今後変更しない。

## 一般AP公式の新候補（未形式化、完成扱いしない）

v>=2。Bをordinary半群Gamma=<v,v+1,...,2v−1>のactual接錐とする。これは既存最大埋込次元cone。基底は1とx^(t−1)z_a (t>=1,0<=a<v、a0はx)で、z_a z_b=x z_(a+b) (a+b<v)、それ以外0。AP変数index jをz_(v−j)へ反転して対応する。AP head基底のindex i=t*v−aにB単項式x^(t−1)z_aを対応。i<mだけ残すactual商B/JがAP headとなるはず。B本体とAP半群環を同型とはしない。

Jの最小次数はceil(m/v)>=2。Bの通常Tor正行はinternal degree i+1に集中（x正則、B/x square-zeroからgraded版で証明する必要あり）。JのTorはdegree>=i+2なのでJ→Bの全Tor写像は0。実LESからbeta_i(A)=beta_i(B)+beta_(i−1)(J)。この消滅は未証明の入力にせず、実gradingから証明する。

xはJ上も正則。M=J/xJは長さvの二次数加群。D=v−((m−1)%v)とし、lower C dimensionD、upper U dimension(v−D)。残りr=v−1変数の作用はHankel型、X_j c_a=d_(j−a)（1<=j−a<=v−D）、upperへは0。この実加群同定を証明する必要がある。

Hankel境界はDelta_p:C⊗wedge^p(k^r)→U⊗wedge^(p−1)(k^r)。p<=Dで全射、p>=Dで単射なら、Mの全Bettiはp+1<=Dで(D−p)*choose(v,p)、それ以外(p+1−D)*choose(v,p+1)。この項とBのi*choose(v,i+1)が元のGSS公式に一致する。

rank候補の完全な線型代数的理由：無限同標数拡大体でr個の異なる点t_jを取る。Vandermonde線型変換後の作用Y_jはu(t_j)*ell(t_j)というrank1。ell(t)=(1,t,...,t^(D−1))、u(t)=(1,t,...,t^(v−D−1))。boundary kernelのあるtarget wedgeH（cardp−1）を見ると、j outsideHのu(t_j)がcard r−p+1<=v−Dなら独立。よって各source wedgeFとj inFについてell(t_j)(c_F)=0。p>=DならこれらellのうちD個が独立でc_F=0。p<=Dの全射はdual同様（sourceFのellが独立、targetH外のuがUを張る）。有限体は実base change/rank保存で戻す。p=Dのsquare matrixには任意標数で可逆性がある。v=DのU=0、v=1は既存二生成元ケースを別に扱う。

/tmp/RankOneIncidence.leanは有限sumでのrank-one incidence写像の単射一般補題のみGREEN（最後のunused instance omit修正後再確認）。これはactual AP公式の証明ではない。まだproductionへ移していない。
