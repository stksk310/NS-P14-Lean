# V05 二つの追加簡約：厳密算術と成果物保持の検証

対象基準は work commit 345e2d82fea50ef89e00a8f35c4fb53ac601d7ce。
既存 V04、本番 Lean、凍結命題、旧証跡は変更しない。
担当変更は checks/verify_reduction.py と本記録だけである。

## 数学の検算対象

**非 antipodal 第一行。** 距離和上界
\[
B_3(u)=u+\sum_{j\ge0}(u-4-3j)_+
\]
で \(u-4=3k+b,\ k\ge0,\ b\in\{0,1,2\}\) と置くと、
\[
B_3=u+\frac{3k(k+1)}2+(k+1)b,\qquad
6B_3=u^2+u+4+b(3-b)\le u^2+u+6.
\]
後半で \(b(3-b)\) は正確に 0,2,2 のいずれかである。
これは整数除算の全剰余を尽くす三場合であり、半群を有限個列挙する代替証明ではない。
一般の \(k,b\) を含む最初の二式を記号多項式として照合した。

既存の actual 第一行からの
\[
\beta_1\le\tfrac52W-u+5\le B(u):=\tfrac5{12}(u^2+u+6)-u+5
\]
に対し、整数容量 \(A(u)=\binom u2+1\) を用いる。
\[
A(u)+1-B(u)=\frac{u^2+u-66}{12}
=\frac{(u-8)^2+17(u-8)+6}{12}>0\qquad(u\ge8).
\]
従って整数 \(\beta_1<A+1\) から \(\beta_1\le A\) となる。
検算はこの一つの恒等式と、\(u=8,\ldots,1000\) の尾和・整数床の転記を確認する。
数学的な全称性は上の非負係数表示と全剰余分割から従う。

**一般の正規化による高次行。** 次の式を
\(e\ge2,\ u\ge e,\ 2\le i\le e\) の範囲に限って用いる。
\[
\mathcal T_i(u)=
\frac{i\binom u{i+1}}{\binom ei}+\frac{ui}{e}
+\frac{(e-i)(e-i-1)}{e(i+1)},\qquad
U_i(B)=B\binom ei-u\binom{e-1}{i-1}-\binom{e-1}{i+1}.
\]
\(\binom ei>0\) を確認してから
\[
i\binom u{i+1}-U_i(B)=\binom ei(\mathcal T_i(u)-B)
\]
へ移す。基点・幅差分は
\[
\mathcal T_i(e)=e-1+i/e,\qquad
\mathcal T_i(u+1)-\mathcal T_i(u)
=i\frac{\binom ui}{\binom ei}+i/e.
\]
\(i<e\) の場合に限り、隣接する二項係数比は
\[
\frac{\binom u{i+1}}{\binom e{i+1}}
=\frac{\binom ui}{\binom ei}\frac{u-i}{e-i}.
\]
その差分比較の係数は
\[
(i+1)\frac{u-i}{e-i}-i
=1+\frac{(i+1)(u-e)}{e-i}\ge1.
\]
この有理式への書換えを記号計算で照合し、base・step・支払い同値性・単調性を
\(e=2,\ldots,40,\ e\le u\le100\) で転記確認した。

上端では \(\mathcal T_e(u)=e\binom u{e+1}+u,\ U_e(B)=B-u\) を直接検査する。
\(i>e\) は \(U_i(B)=0\) であり、正規化関数はその入力を拒否する。
従って \(e-i=0\) または \(\binom ei=0\) による除法を検算自身も行わない。

五生成元への適用では \(e=5,u=8,B=14\) と
\(e=5,u\ge9,B=u^2/4\) を別の second-row seed として残す。
前者は \(\mathcal T_2(8)=74/5>14\)、
\(U_2(14)=104\le2\binom83=112\)。
後者の必要な cubic 差は既存の \(z=u-9\) の正係数式を維持している。
各 seed から \(i=2,3,4,5\) を一般の正規化で支払う転記を
\(u=8,\ldots,500\) について照合した。

## 実行結果と使い分け

原稿・PDF が未組立の段階でも、次のコマンドは読取専用で算術部分を実行できる。

    python3 -B proof_sharp_v5/checks/verify_reduction.py --math-only

実行結果は PASS_V05_ARITHMETIC_TRANSCRIPTION_CHECKS_ONLY。
記号恒等式21件、有限転記検査76,427件、区間分割確認6,660件が通った。
V05 追加分の有限検査の内訳は次の通りである。

| 検査対象 | 件数 |
|---|---:|
| 非 antipodal の正確な尾和・整数 slack | 993 |
| 正規化の基点・幅差分・支払い同値性・単調性 | 57,460 |
| 上端行と上端後の零行 | 3,120 |
| 五生成元の共通正規化による第2–5行 | 1,972 |

この数字は assertion 総数ではなく、スクリプトが明示的に数える入力組の件数である。
一つの入力組で複数の恒等式・境界を調べる場合がある。
有限検査を全称証明の代替にはしていない。

原稿と全組版が揃った後の最終確認は、親担当が次を実行する。

    python3 -B proof_sharp_v5/checks/verify_reduction.py

math-only の成功は、この最終確認が済んだことを意味しない。
最終実行の結果は V05/verification.json に記録される。

## V04・本番証跡・PDF を結び付ける検査

通常モードには既存検査を保ち、次を追加・強化した。

- PREVIOUS_VERSION_SHA256.json の全49項目を照合するだけでなく、
  実際の V04 の全ファイル集合がその49項目と等しいことも確認する。
  新しい想定外ファイルや欠落も検出し、全49ファイルを再 hash する。
- 現在の本番 tracked file が基準 commit と同一であること、および Run18 の
  SOURCE_SHA256 / MANIFEST_SHA256 全項目の byte 同一性を引き続き確認する。
- canonical 本文には七章それぞれが正確に一度、指定順で入っていることを確認する。
  章単体が存在するだけでは stale な canonical 本文を通さない。
- PAGINATION.json の canonical と比較参照本の両出力について、
  source・TeX・PDF の実 SHA256、実文字数、pdfinfo の実頁数を metadata と照合する。
  11pt・単段・A4・余白25mmの組版条件も検査する。
- canonical 一つだけを調べていた旧検査を改め、両出力の実 TeX log と metadata の
  欠字数・overflow数が一致し、ともに0であることを確認する。
  fatal error / emergency stop がなく、PDF出力完了が記録されていることも検査する。

既存 V04 を一切書き換えず、保持された二つの PDF/log を入力にした制御検査で、
正常な両出力を受理することと、第二出力の PDF hash・source hash・TeX hash・
頁数・欠字 metadata・overflow metadata の各改竄を個別に拒否することを確認した。
旧 V04 metadata にない source/TeX hash 欄はメモリ内で補い、
旧ファイル自体を書き換えずに制御検査した。

この担当では新しい Lean 証明を実装・再認証していない。
既存の全 source 行は残し、新稿の紙上統一と、その転記・成果物保持を検査する範囲である。
