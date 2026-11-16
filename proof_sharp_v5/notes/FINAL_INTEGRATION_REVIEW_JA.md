# V04 最終統合レビュー：共通接続・全域合成・依存記録

読解基準：`origin/work` commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
対象は第1章・第6章の全文、各専門章の入口・出口と相互参照、
`DEPENDENCY_AND_COVERAGE_JA.md`、`CHANGE_LEDGER_JA.md`、canonical 結合原稿である。
第2–5章の固有証明は保存された別担当の相互レビューを確認し、同じ証明を最初から再導出してはいない。
本担当は APD 章の著者でもある。APD の新しい整数閾値による統一は ordinary 担当の独立提案と再確認を受けている。
Lean/lake の再実行、原典全文の再取得・全面再査読、既存証跡の変更は行っていない。

## 1 数学的な統合判定

**読解した接続に、全域主定理を妨げる数学的欠落・未処理のパラメータ範囲・任意標数性の誤用は見つからなかった。**
これは紙上の専門章同士が正しい仮定と対象でつながることのレビューであり、
全域 NS-P14 の新しい Lean export や fresh kernel build の認定ではない。
読解 SHA の Run18 COMPLETE が狭幅 \(e\ge5\) の六契約であり、Run19/20 の全域閉鎖 export が未実装である点は
`STATUS_COVERAGE_AUDIT_JA.md` に分離して記録した。

## 2 共通章と全域合成の接続

| 接続 | 確認内容 |
|---|---|
| 元 source | 接錐は元の \(S\)。正規化は \(g_j=m+da_j\) という同じ整数の表示で、別の半群への unit 作用・反射を行わない |
| 完備化 | 各次数の exact order 単項式基底と積が一致し、各原子の初期形と polynomial action を保つ。形式級数環全体の tensor 同型を仮定しない |
| 最小表示 | source はその原子、target は \(m,\ldots,m+\min(w,m-1)\) の実最小系を使う。両側の変数数を等置しない |
| 体 | ordinary の一般 cut のための拡大は同標数。最小自由解消の flat base change で元の体の Betti 数へ戻す。narrow は最初から任意体 |
| 狭幅入口 | \(q=e-2\)、\(u\ge q+1\)、\(d\ge1\)、collective gcd 条件、\(m\ge du+2\) は BRIDGE から端点 EH に渡る。EH の必要条件 \(u<m\) を満たす |
| target | 正規化幅 \(u\) と物理幅 \(du=w\) を区別。容量単調性と actual CAP を使い、full AP は同一 target 又は物理幅で直接払う |
| 容量の範囲 | MINCAP は \(1\le i\le v\)。\(i>v\) に正の下界を課さず actual0 を使う。第3行 LOWCAP の \(v\ge5\) を幅4へ延長しない |
| 小生成元 | \(e=1\) は \(S=\mathbb N\)、空 gcd と \(v=0\) の式を使わない。\(e=2\) は主イデアルの最低次数形、\(e=3\) は LTV と ideal/quotient shift |
| 全域分割 | 整数幅 \(w\ge m-1\) と \(w\le m-2\) は排他的で全域を覆う。ordinary/N4/\(e\ge5\) narrow の出口が第6章の仮定と一致 |

第6章の \(e=2\) の説明では、\(Y^m-X^n\) の最低次数形は \(Y^m\)。
非零の係数形式級数との積でも最低次数形はその積となり、associated graded の定義理想が \((Y^m)\) である。
target 第一行は CAP から \(\binom v2+D\ge1\)、以後 source が0となるため、target の上方消滅を仮定する必要がない。

## 3 原子的境界の確認

| 境界 | 使う経路と、未処理にならない理由 |
|---|---|
| ordinary \(r=2,\delta=0\) | O3 で \(\nu=1,N=T=0\)、空の塔・資源列。O7 の低 rank 評価と O6 の第0 homology 補正をそのまま適用 |
| ordinary relative top | O5/O7 に \(j=r\)、O6 の係数変換に \(c_{r+1}=0\) と H0 補正が残る。最終 \(i=e\) を \(i>e\) と混同しない |
| \(w=m-1\) | ordinary 側に含む。target は \(v=m-1,D=v\)、ORDCAP の列を使う |
| \(u=e-1,i=e\)、full AP \(d=1\) | source と literal target は同じ半群。source の AP 公式では \(i=u+1\) の二項係数が全て0。MINCAP の適用範囲を広げない |
| \(u=e-1\)、full AP \(d\ge2\) | AP source 上界 \(i\binom{u+1}{i+1}\) を \(V=du\ge2u\ge u+1\) の target 第一項が払う。\(F_i^{\min}(u)\) による支払いを要求しない |
| N4 \(u=3,d=1\) | 内部 offset は1,2のみ、full interval source=target。一般上界6や8を正規化幅3の最小容量へ無理に払わせない |
| N4 \(u=3,d\ge2\) | \(V\ge6\)。\((P,\sigma,R)=(3,2,0)\) の四行を物理 target が払う。top source 第4行は0 |
| N4 \(u=4\) | 第2–4行は \((12,5,0)\) と実最小容量 \((12,7,1)\)。第一行の最後の族は N7 の全 \(m\ge6\) 競合証明へ接続 |
| N4 \(u=5\) | 床を保持して \(P\le7\)。小幅の第2–4行表と N5 第一行。一般 cubic の \(u\ge6\) へ混ぜない |
| 五生成元 \(u=6,7\) | 同じ一般行パッケージの十分な上界44/68を target46/77が払う。\(u=7,R>0\) の改善は元の \(H_x\) でのみ使用 |
| 五生成元 \(u=8\) | 第一行 APD は整数閾値で統一。全構造共通の第2行には尾和 \(W\le14\) を保持。両者を混同して tail を全体から除かない |
| \(m=du+2\) | 狭幅の閉条件に含む。端点 EH で必要な \(u<m\) と矛盾せず、\(d=1\) への制限も追加しない |
| \(i=0,i=e,i>e\) | 第0行は両側1、\(i=e\) は ordinary 末端又は端点の \(\beta_{q+2}\le R\) まで証明、\(i>e\) で source0。target の行数は独立 |

各幅の分割は以下で隣接し、穴はない。
\[
\begin{array}{c|l}
e=4 & u=3,4;\ u=5;\ u=6,7,8;\ u\ge9,\\
e=5 & u=4;\ u=5;\ u=6,7;\ u\ge8,\\
e\ge6 & u=e-1;\ u=e;\ e+1\le u\le2e-3;\ u\ge2e-2.
\end{array}
\]

## 4 依存の非循環性

一般端点章は target 比較を仮定せず、実 core・全競合・実核補償から E-TOR、E-ARTIN、E-GEN/E-TWO を供給する。
幅章・N4章がこれを actual 容量へ接続するので、target 比較を前提に source 評価を得る循環はない。

APD.1 は端点因子と候補語 spanning だけによる \(P_C\) 上界。
APD.2 はこの上界、一般四点距離和、E-ARTIN、E-TOR を使う第一行補題であり、
W-FIVE-FIRST の結論も W-FIVE-HIGH も使わない。
APD.3 の高次行への言及は、APD.2 を適用した後の全枝の説明であって APD.2 の証明入力ではない。
従って章単位で往復する参照があっても、補題単位の DAG に循環はない。
一般距離和 W-S1–2 は sparse の追加範囲から切り離され、\(e\ge5,u\ge e-1\) と明示されている。

exact antipodal presentation、厳密 \(P,W,b_1\)、N全角による \(R\) 厳密算出、ordinary 余剰全式、
N4 高次の四次・五次支払い、旧列挙証書は採用本文の必要入力に戻っていない。
元の実核と \(P_C-P_G\)、同じ向きの \(R,H_x\)、unit minor、N4のSC復帰と幅4の両座標は残る。

## 5 台帳・外部参照・形式化状態

`CHANGE_LEDGER_JA.md` は実削減・共通化・保持・既に削除済みの区別を行い、
新しい APD 一式、任意基点 ordinary 差分、新 N4 高次行を状態②として記録している。
既存の同結論 Lean export があることと、新しい紙上証明そのものが追加形式化されたことは区別されている。
N4固有の比較・幅4・小生成元/LTV全域 consumer・最終全域 wrapper の未形式化も隠されていない。

公刊入力7件の URL と版・定理番号は第1章に集約され、専門章で無断の新しい公刊入力を導入していない。
照合は既存登録と使用範囲に対して行い、未読原典を新たに再査読したとはしない。
本文の固有核心を旧稿へのリンクだけで代用する参照は見つからなかった。
全章で表示数式区切りは一致し、106個の明示的な式 tag に重複はない。

## 6 レビュー中の軽微修正

- 共通章：\(m\ge2\Rightarrow v\ge1\)、MINCAP の \(v=i=1\) を明示する指摘は反映済み。
- 幅章：W-S1–2 の一般有効範囲と \(n\ge1\) を明示する指摘は反映済み。証明の変更や追加仮定はない。
- 依存表：APD.2 の入力説明と矢印に実核補償 E-TOR を含める指摘は反映済み。`EG --> AP` と、一般距離和・E-ARTIN・E-TOR の入力記載を再読した。証明本文 APD.6 は最初から E-TOR を使用しており、数学的欠落ではなく依存記録の明確化である。

canonical 結合原稿について、全7章の現在の内容がそれぞれ改変なしで含まれ、順序も
COMMON→ORDINARY→ENDPOINT→WIDTH→APD→N4→SYNTHESIS であることを確認した。
新しい APD.8 の整数閾値も結合原稿に反映されている。
組版ページ数・overflow・欠字数は別途組版出力の観測事項であり、本レビューでは確定ページ数の認定を行わない。

最終照合時の SHA256：

| 対象 | SHA256 |
|---|---|
| `NS_P14_SHARP_PROOF_JA.md` | `6eefcc170f4d32a29bec0e283f6dc1dca61df21f670072bce100dbb79eef4c74` |
| `DEPENDENCY_AND_COVERAGE_JA.md` | `22e22b7d84af00a854eeb6bade10afe6b71befae17198498b8b0168e22c5626d` |
| `CHANGE_LEDGER_JA.md` | `2682883a849a2444e5bb7ce1bcb9badbdb1472d7fe48cb63f7e99842fb95e660` |

担当範囲の未解消所見は **Critical 0 / Important 0 / Minor 0**。
上記判定は記載した数学的接続・coverage・参照と状態区分の範囲に限り、将来の変更や新たな kernel 実行結果を先取りしない。
