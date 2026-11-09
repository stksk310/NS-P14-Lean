# P14 証明構造 V03：置換・保存台帳

2026年11月9日。対象は保存済み [V02 統合稿](../proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md) の全17節。V02 本文・旧コード・旧証書・既存監査報告は変更しない。V03 は [新骨子](P14_PROOF_SKELETON_V03_JA.md) と [依存関係表](P14_DEPENDENCY_MAP_V03.md) によって主ルートを選び直す構造版であり、完全な論文原稿や Lean 認証の完成を宣言するものではない。

## 1. 六つの Part と処分語

新骨子への移行先は次の Part 名で固定する。以下の参照は可変な行番号に依存しない。

| 新配置 | 数学的役割 |
|---|---|
| Part I：主定理と実際の比較対象 | actual source・actual interval completion・公刊入力を固定する |
| Part II：ordinary 側の共通代数 | 一つの cut、一つの資源列から全 relative rank と target 比較へ進む |
| Part III：ordinary 側の全域閉鎖 | cut rank で三分し、Apéry–Sidon＋固定 cutoff scalar を採用する |
| Part IV：narrow-width 側の共通端点理論 | 整数 core と actual kernel を保持して Betti 上界へ進む |
| Part V：narrow-width 側の全域閉鎖 | 五生成元以上・N4・幅4・全高次行を処理する |
| Part VI：全域合成 | 全生成元数・二つの幅領域・任意体・全行を合成する |

「維持」は数学的入力を保つこと、「補強」は必要な途中式を戻すこと、「移動」は役割を変えず再配置すること、「置換」は代替証明を主ルートへ採ることをいう。「主依存から除外」は主定理の推論で呼び出さないこと、「歴史的資料として保存」は旧ファイルをそのまま残すことをいう。後二者はファイル削除を意味しない。

## 2. V02 全17節の判定

各行の「主判定」は一つに定め、部分的な維持・置換・保存は最終列で明示する。

| V02 節・正確な見出し | 主判定 | V03 の配置 | 保持する内容・具体的な変更 |
|---|---|---|---|
| §1 主張・記号・公刊入力 | 移動 | Part I | P14 の actual 比較対象、任意体、total graded Betti 数、公刊入力、interval target 公式を保持。旧 §15 と196組を主依存とする構成案は引き継がず、新しい六 Part の導線へ更新する。 |
| §2 数値座標と非Apéry部分 | 維持 | Part II | numerical basis、\(A=G/xG\)、非Apéry ideal \(N\)、actual Apéry 商 \(Q=A/N\)、\(T=(0:_Gx)\)、jump strata を保持。\(T\cong N\) という全体の加群同型に読み替えない。 |
| §3 最短offset経路だけで総量を評価する | 維持 | Part II | actual 最短経路から資源総量を評価する。後の scalar のために別の source や別 cut の資源へ置き換えない。 |
| §4 一つの線形cutを固定する | 維持 | Part II | Green の次数2入力、\(r=\max(2,p(q_2))\)、一つの cut の固定、同標数の純超越拡大による有限体処理を保持。\(r\ge3\) と \(r=2\) の分岐を Part III への受渡しにも明記する。 |
| §5 実際の塔と一つの資源列 | 補強 | Part II | actual 完全列・tower と同一資源列を保持。同 jump strata、区間計数、\(H_0=\delta\)、\(\sum H_t\le\delta\mathcal V\)、\(H_t\le M\)、\(H_1\le M-a_r\) の共通出所を表示する。 |
| §6 Harmonic評価をKoszul行列から直接証明する | 補強 | Part II | 初項化の境界 rank 比較、単項式商の \(\pm1\) 小行列、harmonic 評価を保持。有理重みは整数 rank の評価であることと、単一次数生成の使用箇所を明記する。 |
| §7 塔から同じcutの全rankへ | 補強 | Part II | A の橋。\(T\) の filtration と同 jump \(K_s\) の比較から Tor の三段不等式鎖を表示。実際の \(d_2\)-rank を保持し、減算される補正項の非負性を記す。 |
| §8 実際のordinary targetへ移す | 補強 | Part II | B の橋。第0 homology の正確な補正、relative Betti 多項式、target 差の係数恒等式と \(R_j\) を明記。top rank と余る非負係数を含め全行十分条件を説明する。 |
| §9 二本と三本のcutをすべて処理する | 移動 | Part III | \(r=2,3\) の直接評価をそのまま採用。\(r=3\) で使う \(q_2\ge6\)、\(H_1\le M-6\) と \(H_1\le3\delta\) を同一資源列上で区別して示す。 |
| §10 四本以上の全rankを一つの数へ還元する | 移動 | Part III（Part II との接続） | \(r\ge4\) の全 rank から \(F_r\) への還元を保持。\(j=2,t=1\) の例外的な重み比較、\(t=0\)、top rank を落とさない。 |
| §11 固定cutoffによるscalar評価 | 置換 | Part III | \(4\le r\le8\) は新しい Sidon＋5行有理表へ置換。既存 scalar は \(r\ge9\) のみ主依存として保持し、rank 9 の行と rank 10 以上の普遍的 barrier 証明を残す。旧 \(r=4,\ldots,8\) anchor は V02 内の歴史的導出として保存する。 |
| §12 共通端点模型とactual接錐への移行 | 補強 | Part IV | core の整数座標、全長競合、\(N_s=M_s\cap T_s\)、端点 homology、actual kernel 補償を保持。C の carry 相殺を三行で表示。\(Q_C\to Q_G\) の核長を消さずに全 Betti 行へ移す。 |
| §13 五生成元以上の幅側 | 移動 | Part V | 各幅領域の第一行・高次行・小境界処理を保持。dense 幅では target 第一項との一つの差 \(\mathscr D_i\) と Vandermonde の支払いを補う。Part IV の actual kernel 補償付き上界を参照する。 |
| §14 四生成元の真正狭幅 | 置換 | Part V | §14.1–14.3 の端点基礎・Kneser 距離和・Savchev–Chen の混合語評価、§14.4 の全高次行、§14.6 の局所的な幅4全 \(m\) の Gröbner 証明 (N23)–(N28) を保持。§14.6 末尾の「有限196対を合わせる」という旧 N4 全域合成は保持しない。旧 §14.5 の196組部分を紙上の一括計数と幅6–8の代数的場合分けへ置換。D の競合座標と初期 ideal の等号を補強する。 |
| §15 小ordinary領域：83組と5本の無限tail | 主依存から除外 | V03 主証明の配置なし。歴史的資料として V02 に保存 | first-hit 最大化、actual-to-formal 変換、truncated lex、83組 profile 比較、665行 Betti 比較、5本の tail の全系統を主ルートで呼び出さない。Navi の別証明を読む場合に限り必要部分を参照する。 |
| §16 全領域の合成 | 置換 | Part VI | 旧 §16 の全域合成全体を、新しい各枝の閉鎖を受け取る合成に置換する。\(e=1,2\) の基礎計算、\(e=3\) の公刊入力、整数幅の排他的・網羅的な分割は再利用する。ordinary を \(r=2,3\)、\(4\le r\le8\)、\(r\ge9\) に更新し、旧「\(e\ge10\) は §11、\(5\le e\le9\) は §15」という分岐を除く。幅側も196組を参照しない。 |
| §17 計算支援部分と形式化の境界 | 置換 | Part VI 後の監査境界、および [査読準備表](P14_REFEREE_READINESS_V03.md) | 196組と83組を「必須証書」とする一覧を引き継がない。紙上恒等式・有限有理表・代数的場合分け・公刊定理・回帰計算を区別し、内部レビュー、外部査読、Lean 認証の境界を明示する。 |

## 3. ordinary 置換の正確な範囲

採用するのは [ordinary 紙上置換](../auditability_search/ORDINARY_PAPER_REDUCTION_JA.md) の (SO1)–(SO5)。論理的な入口は Part II の同じ actual \(Q\) と同じ資源列である。

\[
q_2=\binom e2\Longrightarrow m\ge e(e-1)+1
\Longrightarrow\delta=m-e\ge(e-1)^2.
\]

この含意は actual numerical Apéry quotient についての主張である。actual cut の \(r=e-1\) から最大二次層を導く際には **\(r\ge3\)** を必要とする。\(r=2\) は旧 §9 の直接評価で処理する。

\(4\le r\le8\) は固定 cutoff の二変数恒等式

\[
G(r+1+s,a_r+t)=g+sA+tb+(1-\alpha)
\left(\binom t2+st\right)
\]

と5行の有理表で閉じる。\(r=4,5\) は \(g>0\)、\(r=6,7,8\) は \(A,b,1-\alpha>0\)、\(g+A,g+b>0\) とし、残る負の角 \(s=t=0\) を actual Apéry–Sidon 補題で排除する。旧 §11 の小 rank の5行を新表に重ねて主証明へ入れない。\(r\ge9\) には旧 §11 の rank 9 行・大 rank 証明を保持する。

これにより除外するのは83組の証書だけではない。旧 §15.1–15.4 の証明系統そのものが Part VI への必須依存から外れる。BHP/EK は Part V の dense 幅に引き続き必要であり、旧 §15 の除外から公刊 BHP/EK 入力の除外は導かない。

## 4. N4 置換の正確な範囲

[N4 紙上置換](../n4_further_reduction/N4_PAPER_REDUCTION_JA.md) を採用する。対象は任意体、\(d\ge1\)、\(0<a<b<u\)、\(\gcd(a,b,u)=\gcd(m,d)=1\)、\(m\ge du+2\) の全域であり、target の幅は物理幅 \(V=du\) である。

| 対象 | V03 での扱い |
|---|---|
| 共通端点理論、actual kernel、\(R\le\min\{W-u,u\max(H_x-2,0)\}\) | 必須として保持する |
| Kneser の距離和 \(W\le1+\lfloor u^2/4\rfloor\) | 必須の公刊入力とその適用証明を保持する |
| Savchev–Chen による混合語 \(s+t\le\lfloor u/2\rfloor\) | 必須として保持する。unit 変換を actual source の Betti 不変性と解釈しない |
| \(u\ge9\) の第一行 | 三つの端点関係、禁制長方形、downset の計数、socle 上界による一括紙上評価へ置換する |
| \(u=5,6,7,8\) の第一行 | height・差 \(b-a\)・gcd による有限の代数的場合分けを保持する |
| \(u=3,4\) | source=target、小 dilation 比較、非境界対、境界対を分ける |
| \(d=1,u=4,(a,b)=(1,3),m\ge6\) | V02 §14.6 の (N23)–(N28) と局所的な全 multiplicity Gröbner・四剰余証明を保持し、競合座標を補う。同節末尾の196組を用いる旧 N4 合成文は採らない |
| 全高次行 \(i=2,3,4\) | V02 §14.4 の紙上比較を保持。第一行の新計数から自動的に済むとは記さない |
|196 oriented offset 対の機械証書 | 主依存から除外し、旧ファイル・回帰資料として保存する |

したがって「196組の機械計算が主依存から外れる」は正しいが、「有限の場合分けが一切なくなる」「Kneser・Savchev–Chen・幅4が不要になる」は採用しない。

## 5. Navi の独立代替証明

[Navi クロスレビュー](../navi_cross_review/NAVI_CROSS_REVIEW_JA.md) の (NI1)–(NI10) と [増分補題のレビュー](../navi_cross_review/INCREMENT_REFEREE.md) は別資料として保存する。\(0\le\Delta B_1(e,m)\le m-2\) の紙上証明は得られており、「未証明の増分予想」という古い評価へ戻さない。

ただし、この別証明が83組・5 tail を置換しても、actual source への鎖

\[
\beta_i(G)\le L_i(h,\rho)\le L_i(\widehat h,\rho)
\le L_i(\widehat h,m-1)=B_i(e,m)
\]

は保持される。旧 (O1)–(O4)、(O6)–(O13) の停止・truncated lex・first-hit 最大化が必要であり、形式的な profile の実現を仮定する必要はない。この依存が残るため、Apéry–Sidon 主ルートと二重に組み込まない。全行帰納の top 行・第0行・source の表示変数数を超える行の処理も、独立代替資料内で維持する。

## 6. 保存方針と今回の検証の境界

V02、`proof_integrated_v2/checks/`、`proof_integrated_v2/certificates/`、既存 `proof_complete/`、`proof_reduction/`、`simplification_search/`、`n4_further_reduction/`、`auditability_search/`、`navi_cross_review/` を保存する。旧 proof route が正当化できることと、V03 で必須とすることは別である。既存 manifest やハッシュは版の同一性の証拠であり、補題の数学的正当性を代行しない。

今回必要な確認は source の同一性、新5行 scalar 表と恒等式、N4 の置換依存、A–D の橋、全パラメータ・任意体・全行、全17節からの参照の完全性に限定する。必要な三つの算術 checker は一回ずつ実行され、[査読準備表 §5](P14_REFEREE_READINESS_V03.md) に結果と旧小 rank 診断の非依存性を記録した。最終構造点検と同一性の採録後は新しい大規模探索や旧証書の反復再実行を行わず固定する。新骨子の依存関係で旧 §15・196組・Navi を「保持資料」として参照することは、主定理の必須前提として参照することと区別する。

検証の実行結果と残る外部独立検証・Lean 作業は [査読準備表](P14_REFEREE_READINESS_V03.md) と併読する。この台帳自体は新しい全体査読や形式認証を行ったという記録ではない。
