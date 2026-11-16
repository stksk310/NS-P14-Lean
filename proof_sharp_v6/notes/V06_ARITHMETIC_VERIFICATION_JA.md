# V06：全競合高さと dense 統合の検算・保持記録

基準 commit は 345e2d82fea50ef89e00a8f35c4fb53ac601d7ce。
担当編集は checks/verify_reduction.py と本記録のみである。
本番 Lean、V04 全49ファイル、V05 全55ファイルは変更していない。
既存 V05 の76,427件の転記検査と21記号恒等式は全て維持した。

## 1　carry 表を使わない全 j の高さ

\(u<m,\ 0\le r,s<u,\ j\ge1,\ d\ge1\) とし、
\(s=(r+jm)\bmod u,\ c=(r+jm-s)/u,\ \epsilon_r=[r>0]\) と置く。
整数の天井関数の平行移動と単調性から
\[
\begin{aligned}
c-\epsilon_r+\epsilon_s
&=\left\lceil\frac{r+jm}{u}\right\rceil-\left\lceil\frac r u\right\rceil\\
&\ge\left\lfloor\frac{jm}{u}\right\rfloor\ge j.
\end{aligned}
\]
最後は \(m>u\) による。従って \(L\le H_x\) に対し
\[
\max\{0,L-jd-c+\epsilon_r-\epsilon_s\}
\le\max\{0,H_x-2j\}.
\]
括弧内は整数差として全体を計算し、その後一度だけ0で切る。
途中の減算を自然数の飽和減算で置き換えない。

検算は \(3\le u\le24\) における複数の \(m>u\)、\(j\)、全 \(r\)、
複数の \(d,H_x,L\) を用い、上記等式・不等式・clamp を照合した。
\(r=0\)、\(s=0\)、\(\gcd(m,u)>1\)、\(m=u+1\)、\(H_x=0,2\)、
一般の \(H_x\le2\) が実際に含まれたことを別フラグでも確認した。
不等式は \(\gcd(m,d)=1\) 自体を必要としないため、その条件を課さないより広い
整数座標でも検査している。有限座標の検算を、actual 半群の全称証明と混同しない。

固定した行先 \(s\) に対しても、十分大きい \(j\) を選び
\(r=(s-jm)\bmod u\) とした始点の第一座標が0となることを照合した。
ここで周期 \(u/\gcd(m,u)\) を選ぶ必要はない。
本文が保証する各 \(M_r\ne0\) を合わせることにより、
各 \(T_s\) が純粋な \(v\) 冪を含むという紙上証明へ接続する。

有限生成について、checker は有限個の \(j\) から普遍性を推測しない。
紙上証明は、全 \(j\) の始点の第一座標が
\(\{0,\ldots,\max(H_x-2,0)\}\) に入ることを先に証明し、
各第一座標で第二座標の最小値を一つ取るものである。
これにより無限個の競合から生成される実際の \(T_s\) が有限生成となる。
明示的な周期停止次数を証明する数学的仕事は不要になる。

独立補助担当も、天井式、零剰余、非互除、最小の \(m=u+1\)、小さい \(H_x\) を再読し、
追加の境界除外は不要と報告した。
既存 Lean の Carry.carry_epsilon_lower / floor_jm_ge / forbiddenStart_height
と同じ不等式を使うが、新しい紙上構成全体の形式認証を今回行ったものではない。

## 2　dense の t=3 と t≥4 を一つにする

\(q\ge4,\ 3\le t\le q\) に対し
\[
c_{\mathrm{dense}}=\frac{5t^2-17t-6}{6}+(t-1)(q-t)
\]
の恒等式
\[
6c_{\mathrm{dense}}
=12(q-4)+5(t-3)^2+(t-3)+6(t-3)(q-t)\ge0
\]
を SymPy で記号的に照合した。
各項の非負性は本文で全範囲に証明されており、有限検査からの外挿ではない。
\(q=4,t=3\) では係数は正確に0であるため、「正」と強めない。

全 \(1\le i\le q+2\) について、記号
\[
A_i=\binom{q-1}{i-1},\quad C_i=\binom q{i-1},
\quad B_i=\binom{q+1}{i-1}
\]
を使い、許される最悪の資源
\(P=q+1+2t,\ R=t,\ K=2t(t-1)/3\) を代入した。
その容量差
\[
\mathscr D_i=
i\left[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}\right]
-(q+1+2t)C_i-tB_i-\frac{2t(t-1)}3A_i
\]
が \(c_{\mathrm{dense}}C_i\) 以上かつ非負となることを
\(q=4,\ldots,40\) の全該当 \(t,i\) で転記確認した。
\(K\) の有理上界は体内で割ることではなく、整数個数への数値上界である。

上端 \(i=q+2\) では \(A_i=C_i=0,\ B_i=1\) を明示的に確認し、
0になる二項係数による除法を行わない。
最小の \(q=4,t=3,i=1\) では容量差も正確に0である。
残す \(t=2\) の枝は \(R=0,K=2\) を使い、
\[
\mathscr D_i\ge(q-3)C_i+iB_i-2A_i\ge0
\]
を同じ全行範囲で別に検査した。ここでも \(q=4,i=1\) の差0を含む。

## 3　実行した算術検算

原稿・PDFの組立中でも次はファイルを書き換えずに実行できる。

    python3 -B proof_sharp_v6/checks/verify_reduction.py --math-only

結果は PASS_V06_ARITHMETIC_TRANSCRIPTION_CHECKS_ONLY。
記号恒等式22件、有限転記検査366,959件、区間分割確認6,660件が通った。
有限転記件数は V05 の76,427件と以下の V06 追加分の合計である。

| V06の追加対象 | 入力組数 |
|---|---:|
| carry の天井等式・床下界 | 8,880 |
| 整数差全体を一度 clamp する高さ評価 | 237,600 |
| 固定した行先剰余と十分大きい j | 21,186 |
| dense 統合枝の全正行 | 21,978 |
| 残す dense t=2 の全正行 | 888 |

一つの入力組で複数の assertion を調べる場合があり、
この表は assertion 総数ではない。
有限検査は数式の転記と境界確認であり、全称的な紙上証明の代替ではない。

## 4　元資料・既刊成果物と新しい組版の保持

通常モードは、全原稿・組版が揃ってから親担当が実行する。

    python3 -B proof_sharp_v6/checks/verify_reduction.py

V06では保存先と比較先を明確に分けた。

- PREVIOUS_VERSION_SHA256.json：V05全55ファイル。
- ANCESTOR_V04_SHA256.json：V04全49ファイル。

両方ともファイル集合の完全一致と全項目の byte hash を検査し、
この担当でそれぞれ55件・49件の成功を独立に確認した。
本番 tracked file と旧 Run18 source/evidence manifest の既存全項目検査も維持する。

V06の二つのPDFは引き続き、各source・TeX・PDFの実 SHA256、
実文字数、pdfinfoの実頁数、実ログの欠字数・overflow数とmetadataを照合する。
いずれのログも欠字・overflowが0であることを要求する。
PAGINATION の revision は V06、previous_revision の実比較先は V05 として検査する。
V04/V05のファイルを再組版したり書き換えたりしない。
保持されたV05の両PDFを読取専用の正常入力として受理し、
第二出力のPDF/source/TeX hash、頁数、欠字数、overflow数の六つの誤値を
メモリ内で個別に与えた制御検査は、すべて拒否した。

編集上の依存guardでは、全 j の実核 E5–E7、高さ E8、資源 E9–E11、
実homology E12、核補償 E13、E-TOR のラベルが保持され、
明示的 E-STOP と \(J_0+p\) が戻っていないことを確認する。
他章に E-STOP の参照がなく、幅4の独立した全競合議論 N7b–N7d が残ることも確認する。
このguardの独立実行は成功した。
ラベルの検査は数学的真性の判定ではなく、意図しない削除・依存再流入の検出補助である。

この時点の math-only 成功を、最終通常モードや新PDFの完成と読み替えない。
最終結果は親担当の実行後に V06/verification.json へ保存される。
本担当は新しい Lean 証明の実装・再認証を行っていない。
