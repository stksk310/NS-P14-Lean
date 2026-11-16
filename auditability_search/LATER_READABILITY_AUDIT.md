# 後半の数学的監査負担：限定点検

2026-11-09。対象は保存済み V02 `proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md` の §§11–17 と、`n4_further_reduction/N4_PAPER_REDUCTION_JA.md`。本稿は原稿・既存コード・既存証書を変更しない。以下の行番号はこの二つの原稿の現行行番号である。

**判定。今回追った箇所には、結論を阻む数学的な欠落を発見しなかった。** ただし、有限証書の縮小後にも、actual 核の構成、端点からの移行、dense 幅の容量比較には人間が再構成しなければならない中間計算が残る。ここでは「省略されているが再構成すると成立する」箇所と、依存版の取り違えを分ける。公刊定理そのものの再査読や Lean 認証は行っていない。

優先順位は、新しい証明ルートを読む人に残る負担を基準とする。普通領域の 83 組を別の有限表に作り替える探索は行っていない。

## 1. 最優先：端点 corner 評価の carry 相殺を一式で見せる

**場所。** [V02:976](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:976)–[991](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:991)、特に 986–988 行。

**区別。** これは真の gap ではない。`(E17) を足すと` の一言が、三種類の数を相殺して `R≤W−u` にする肝心な計算を隠している。ここを読み飛ばすと、core の距離和が unrestricted な actual source の socle を抑える理由が証書の経験則に見えやすい。

最短点 `(L_r,K_r)` に `j=1` の競合を適用し、生成元を `(A_r,B_r)`、行き先を `s_r` とする。本文の定義から

\[
s_r=(r+m)\bmod u,\quad c_r=(r+m-s_r)/u,
\quad A_r\le L_r,\quad B_r=K_r+c_r.
\]

`r↦s_r` は置換なので `Σ_rc_r=m`。さらに `(E17)` は `Σ_sκ_s≥m` を与える。したがって省略された計算は正確に

\[
\begin{aligned}
\sum_s z_s
&\le\sum_r(A_r+B_r-\kappa_{s_r})\\
&\le\sum_r(L_r+K_r)+\underbrace{\sum_rc_r}_{m}
                   -\underbrace{\sum_s\kappa_s}_{\ge m}\\
&\le\sum_r(\ell_r-\epsilon_r)=W-u.
\end{aligned}
\]

`Σ_s ceil((m−s)/u)=m` も、`m=hu+t, 0≤t<u` と書けば、`s<t` で `h+1`、残りで `h` なので `t(h+1)+(u−t)h=m` となる。

**最小の展開。** 上の三行の不等式を 987 行の代わりに置き、直後に既存の socle 単射を接続する。この相殺が済んで初めて `R≤Σ_sz_s≤W−u` となる。第二の上界は各 `T_s` の第一座標が `0,…,max(H_x−2,0)` に入るため `z_s≤max(H_x−2,0)` であり、これは別の理由である。二つを混ぜない方が検証しやすい。

## 2. 最優先：幅4で「全競合を尽くした」ことを座標で確認する

**場所。** [V02:1836](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1836)–[1866](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1866)。N4 置換稿も [169](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:169)–179 行でこの証明を保持するため、196 行証書を外しても監査負担は残る。

**区別。** 記載された閾値と先頭 ideal の等号は成立する。弱いのは結論ではなく、1844–1845 行の `競合条件は厳密に` に至る二つの座標式が省略されている点である。この箇所は特定の multiplicity の実験で代替できない。

短い標準単項式を `x^Lv^Kb`、基点 `b` の次数・offset を `(c,n)` とする。長い表示を自由 anchor `b_{r_j}` と端点で書いたとき、その端点指数は

\[
K'=K-\kappa_j,\qquad
L'=L+c+j+\kappa_j-\lambda(r_j)=L-\Delta_j.
\]

第一式は offset の等式 `r_j+4K'=n+4K−jm`、第二式は長さの等式から来る。したがって非負条件がちょうど `K≥κ_j, L≥Δ_j` となる。本文の `(N26)` は `Δ_j<0` を示すので `L` の制約が消える。制限列 `z²` による競合は `K≥κ_j+1` を必要とし、自由列がすでに覆う。`κ_j` は `j` とともに非減少なので `j=1` が正確な閾値を与える。

**最小の展開。** 上の `L',K'` の二式を追加し、証明の最後を次の二段に分ける。

1. 追加禁止された標準単項式は最大分解長が増えるので actual 接錐で 0 となる。
2. 非禁止の標準単項式は最大分解長が元の次数に等しく、同次数では次数・offset の独立性により像が独立である。

これで「上界候補 `J`」から「厳密な `in(I_G)=J`」への飛躍がなくなる。その後の `μ(I_G)≤μ(J)` は 1863–1866 行の停止除算で既に直接証明されており、一般商の Betti 単調性を補う必要はない。

## 3. 高優先：dense 幅の Vandermonde 支払いを一つの差で統一する

**場所。** [V02:1342](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1342)–[1369](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1369)。

**区別。** ここも gap ではない。`target の第一項`、`最初の二つの非負増分`、`二項係数を比較すると` という三段の圧縮があるため、読者は比較している差を自分で復元する必要がある。第二項の target 補正を使ったのかどうかも、一読では判別しにくい。実際には target 第一項だけで成立する。

\[
C_i=\binom q{i-1},\quad B_i=\binom{q+1}{i-1},
\quad A_i=\binom{q-1}{i-1}
\]

と書くと、追う差は一つだけでよい：

\[
\mathscr D_i=i\!\left[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}\right]
 -(q+1+2t)C_i-RB_i-KA_i.
\]

Vandermonde の `j=1,2` の項はそれぞれ

\[
t\,i\binom{q+1}i=t(q+1)C_i,
\qquad i\binom t2 B_i.
\]

これにより本文の三分岐は次の形で追える。

- `t=2,K≤2,R=0` では `𝒟_i≥(q−3)C_i+iB_i−2A_i`。上界 `K=2` を代入した差ではこれは等式である。
- `t=3,K≤4,R≤3` では `𝒟_i≥(2q−4)C_i+(3i−3)B_i−4A_i`。残りは `i binom(q+1,i−2)≥0` である。
- `4≤t≤q` では、`K≤2t(t−1)/3,R≤t` と `B_i≥C_i≥A_i` を用い、`i binom(t,2)−t≥t(t−3)/2≥0` なので

\[
\begin{aligned}
\mathscr D_i
&\ge\left((t-1)(q+1)-2t+\frac{t(t-3)}2
                        -\frac{2t(t-1)}3\right)C_i\\
&=\left[\frac{5t^2-17t-6}{6}+(t-1)(q-t)\right]C_i.
\end{aligned}
\]

これは本文の係数に一致する。範囲外二項係数を 0 と読む約束により、上端 `i=q+2` でも不等式は有効である。

**最小の展開。** 差 `𝒟_i` と最後の二行を加える。`t=2,3` の既存の短い説明は維持できる。多項式をさらに全面展開する必要はない。

補助的に `4≤q≤24, 2≤t≤q, 1≤i≤q+2` の 5,138 点で上記の等式・不等式を整数と `Fraction` により独立照合した。これは転記検査であり、無限範囲の根拠は上の恒等式と係数の符号である。

## 4. 高優先：証書をなくす場合は §15 の難所を展開せず依存から外す

**旧稿の場所。** [V02:1974](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1974)–[2041](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:2041)。特に `(O11),(O12)`、負 slot の個数、最後の slot が EK 重み付きで全損失を払う 2004–2039 行。

**区別。** 対象の式を追った限り、ここに反例や未処理の場合は見つからなかった。難しい点は単なる代数ではない。actual Hilbert 列から formal envelope への移行、異なる first-hit 間の直接比較、負の小 slot と正の最終 slot の補償という三つの論証を重ねている。

本探索では、この箇所を長文化する提案を優先しない。[Ordinary 置換案](/workspace/NS-P14-Lean/auditability_search/ORDINARY_REDUCTION.md:181) は、独立に検証・採用されれば §§2–10 と小 rank の五つの scalar anchor により §15 全体の依存を外す構成である。削除対象は 83 組の機械比較だけでなく、この first-hit 最大化論証と無限 tail の仕組みも含む。

ただし新ルートにおける actual source の役割は消えない。同置換案の [23](/workspace/NS-P14-Lean/auditability_search/ORDINARY_REDUCTION.md:23)–79 行にある「actual Apéry 商の二次成分が完全なら `δ≥(e−1)²`」を保持しなければならない。負の基点を持つ三 anchor の `s=t=0` を排除する理由がこれであり、formal Hilbert 列が数値半群で実現するという仮定で置き換えてはならない。

旧ルートを残して読む場合、[1984](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1984)–1990 行が既に明示するとおり、formal envelope の数値半群としての実現は不要である。83 組の証書は source の実例の分類ではなく、すべての actual 列を抑える整数式の検証である。この区別は正しく記載されているため、未証明の実現問題として扱わない。

## 5. 中優先：N4 の新しい計数で機械証書が不要になる理由を一段だけ明示する

**場所。** [N4 置換稿:49](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:49)–[94](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:94)、幅 6–8 は 98–154 行。

三つの端点関係、禁じられた長方形、socle antichain の論証は有効である。以下の二点だけを展開すると、旧証書の最大値を使っていないことを手で確かめやすい。

- 純軸は `y^b=0,z^(u−a)=0` なので、単位元を一度数えた個数は `1+(b−1)+(u−a−1)=2u−k−1`。第三関係の倍数は `s=u−b+i,t=a+j` と書き、`i,j≥0,i+j≤h−k` だから、混合三角形から除く個数は `binom(h−k+2,2)` となる。これで `(P4)` の二つの項が別々に確認できる。
- 幅 6–8 の socle 上界は「一方向の指数が `c−1` 以下の downset の antichain は高々 `c` 点」という包含だけで得られる。幅 7 の一辺 2（124–126 行）、幅 8 の一辺 2 または 3（143–150 行）がその適用箇所であり、exact core を計算した結果ではない。

**最小の展開。** `(P4)` の直前に最初の二式、幅 7 の説明の直前にこの strip の antichain 原理を一文入れる。幅 8 の各対をさらに個別の core 表へ戻す必要はない。

元の向きの `H_x,R` と反射した core の不変量を混同していないことは、[33](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:33)–34 行に明記される。幅 6 の height 分岐 100–103 行も元の向きのままであり、反転した別 source の `R` を使う gap はない。

## 6. 依存版と記号の監査

**依存版。** V02 は保存された歴史的版として整合している。196 対が必須という記述は [1589](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1589)、[1773](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1773)、[1889](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1889)–1891、[2165](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:2165)–2171 行に残る。置換稿は冒頭 [3](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:3)–6 行で変更しない版を明示し、[181](/workspace/NS-P14-Lean/n4_further_reduction/N4_PAPER_REDUCTION_JA.md:181)–183 行で新しい依存の除去を主張する。この二つは矛盾しない。

将来の統合版を作る際には、第一行だけを貼り替えて §17 を残すと、不要になった証書を必須と誤認する状態になる。主定理が選ぶ proof route、§16 の合成、§17 の必須依存表を同じ版に揃えることが必要である。これは原稿の現在の数学的 gap ではなく、未統合の置換証明を引用する際の版管理課題である。本稿では書き換えていない。

**記号。** 次の再利用は節ごとに宣言されているので、現状では論理的な不備ではない。ただし、scalar と narrow-width の式を横に置いて監査するときには区別が必要である。

| 記号 | V02 内での意味 | 正確な宣言位置 |
|---|---|---|
| `d` | §11 は multiplicity deficit `δ`、§12 以降は正規化 dilation | 553 行、819–824 行 |
| `D` | §11 は固定 cutoff、§14 は標準内部語の downset、§1 は target 剰余パラメータ | 557 行、1598 行、90 行 |
| `𝒱` と `V` | 前者は資源総量の係数、後者は物理幅 `du` | 556 行、1582 行 |
| `q` | §12–13 は内部変数数、§14.6 の表では `m=4q+r` の商 | 819・834 行、1879 行 |

最小限の対処は、新しい scalar 補題では `d` へ置き換えず `δ` を保つこと、幅4表では `m=4Q+r` と別名にすること、将来の統合版の切替箇所に局所スコープを明示することである。既存式を全面改名する作業は、この監査で推奨する優先作業ではない。

## 7. 展開を増やす必要が薄い箇所

- **§11 の scalar algebra。** 615–628、664–675、735–805 行は、恒等式と符号分解がすでに表示されている。`D` を固定したまま差分を取る点も 563、787 行に明記される。`S28→S30` は等差数列の有限和であり、新たな analytic argument はない。人間の手計算負担は残るが、同じ多項式をさらに展開しても数学的な依存は減らない。
- **実際の `Q_C→Q_G`。** 999–1018 行では actual 核の長さ `P_C−P_G` を Tor 完全列で補い、端点 homology の長さを使っている。`P_C=P_G` や quotient の Betti 単調性を仮定する gap はない。
- **全高次行への移行。** 1460–1473 行の正規化 `𝒯_i(u)` は基点と全増分を比較し、上端 `i=e` も含む。2094–2101 行の旧 ordinary tail も正規化比を明示する。いずれも「第二行が済んだから残りも明らか」という未証明の飛躍ではない。

残る監査負担の中心は、有限ケース数よりも、actual 表示と core 模型の間で何を保ち、何を長さ上界に置き換えたかを追うことである。上の三つの中間計算を補い、不要となる §15 の proof route を外す方が、追加の大量計算表より効果が大きい。
