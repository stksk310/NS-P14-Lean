# V05→V06：denseの三枝を二枝へ

読解対象の本番Leanは commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
V05の原稿と証跡を保持し、V06では幅章W-DENSEの支払い部分だけを変更した。
この追加では公刊入力や新しいrank定理を増やさない。

## 正確な置換命題

整数q≥4、3≤t≤q、1≤i≤q+2と、非負有理数P,R,Kを取る。
\[
 P\le q+1+2t,\qquad R\le t,\qquad K\le\frac{2t(t-1)}3
\]
なら
\[
 \begin{aligned}
 i\binom{q+1}{i+1}+P\binom q{i-1}
 +R\binom{q+1}{i-1}+K\binom{q-1}{i-1}
 \le i\binom{q+t+1}{i+1}.
 \end{aligned}
\]
二項係数は範囲外で0とする。これは容量の数値補題であり、係数体内の除法を含まない。

**証明。** 本文(W-D4)の差と同じく、左辺から第一項を分離し、
\(A_i=\binom{q-1}{i-1},C_i=\binom q{i-1},B_i=\binom{q+1}{i-1}\) と書く。
Vandermondeの最初の二項と資源上界から、容量との差は
\[
 \begin{aligned}
 \mathscr D_i
 &\ge\{t(q+1)-(q+1+2t)\}C_i
      +\{i\binom t2-t\}B_i-\frac{2t(t-1)}3A_i\\
 &\ge\left\{t(q+1)-(q+1+2t)+\frac{t(t-3)}2
                     -\frac{2t(t-1)}3\right\}C_i
 =cC_i.
 \end{aligned}
\]
第二段ではi≥1、t≥3により \(i\binom t2-t\ge t(t-3)/2\ge0\)、
および \(B_i\ge C_i\ge A_i\ge0\) を使った。
整理したcは本文と同じ
\(c=(5t^2-17t-6)/6+(t-1)(q-t)\) であり、
\[
 6c=12(q-4)+5(t-3)^2+(t-3)+6(t-3)(q-t)\ge0.
\]
各項の非負性はq≥4、t≥3、q≥tから従う。従って全指定行で差は非負。
\(C_{q+2}=0\) でもこの議論はそのまま成立し、Cでの除法を必要としない。□

## 元のdense資源への適用と削減内容

本文のdense仮定はq≥4、2≤t≤qである。t≥3ならr=t≤qを選べ、
\(\binom{t+1}2=t(t+1)/2\ge2t\) である。
同じ全Hilbert関数を持つ一つのlex商の親子調和評価(W-D3)から
K≤2t(t−1)/3を得る。元のsourceのP≤q+1+2t、R≤tは(W-D1)のまま使う。
従って上の数値補題が全3≤t≤qを同時に払う。

V05のt3専用式
\((2q-4)C_i+(3i-3)B_i-4A_i\ge0\)、およびt≥4を4+zから始める正係数式は不要になる。
それらを必須付録へ移したのではなく、主定理に至る数学的な場合分けを三つから二つへ減らした。

t2は独立に残す。この境界ではr3、K≤2、元のR=0を使い、一般のt≥3上界を無理に適用しない。
q3のu6/7で使う(W-D1)の資源と第一行改善は変更しない。
q≥4という新係数の仮定をq3へ広げていない。
元のRとHx、QCとQGの区別、核の長さによるTor補償、任意標数のBHP/EKと整数の有理重み計数も保持した。

## Lean対応と未実装部分

| 役割 | 既存export | V06との関係 |
|---|---|---|
| 元のdense資源 | `NSP14.Endpoint.Data.dense_resources` | そのまま使用。q3の既存consumerも維持 |
| 一つのlex商のKとtail評価 | `NSP14.Endpoint.Data.dense_lex_correction_bound` | r=t、3≤t≤qに必要な仮定を満たし、同じ上界を与える |
| Kの全行core評価 | `NSP14.Endpoint.Data.dense_core_lex_bound` | 既存型はt2/t3/t≥4を分けるが、t3のK≤4とt≥4の3K≤2t(t−1)を合わせればV06の必要強度に達する |
| Vandermondeの二項下界 | `NSP14.Width.choose_add_two_terms` | そのまま使用 |
| 既存の係数・支払い | `NSP14.Width.dense_large_coeff`; `.dense_payment` | 既存はt≥4、またはt3専用枝を含む証明。V06の統一係数exportではない |
| 元sourceとliteral targetの比較 | `NSP14.Endpoint.Data.actual_dense_firstterm`; `NSP14.NumericalSemigroup.narrow_dense_comparison` | 同じ結論は既存形式化済み。型の変更は不要 |
| 上のq≥4,t≥3統一係数と全行支払い | 新規named exportなし | **紙上証明済み・新経路未形式化** |

後でLeanへ入れる場合、必要な純算術入力は
q≥4、3≤t≤q、3K≤2t(t−1)、2c0=t(t−1)であり、
`q+1+3t+K ≤ t*(q+1)+c0` という係数不等式に包装できる。
これは既存 `dense_large_coeff` の必要範囲をq≥4,t≥3へ広げた形である。
その後、既存Vandermonde二項下界と同じ行資源を使うconsumerを、t2/t≥3の二枝へ置換できる。
今回、本番Lean・import graph・凍結命題・過去証跡は変更していない。

## 今回の検証

SymPy 1.14.0により、cの整理、上の非負係数恒等式、r=tの二次語容量の差の三恒等式を記号的に確認した。
さらにq4–60、全3≤t≤q、全1≤i≤q+2で、最大の有理数K=2t(t−1)/3をそのまま用いた差の下界を厳密計算し、73,568組すべて成功した。
t3、q4、上端i=q+2のいずれかに当たる3,596組を含む。
有限検算は転記・境界の補助確認であり、全称性は本文のVandermonde下界と上の恒等式で証明する。

変更前のt3枝開始より前と、dense閉鎖文より後は、V05の04章とbyte同一であることを確認した。
従ってt2、q3のu6/7、W-HIGH、non-antipodal第一行、sparse、端の二幅、coverageは保持されている。
APD章とN4章もV05とのbyte同一性を確認した。
今回Lean/lakeのfresh buildは行っていない。
