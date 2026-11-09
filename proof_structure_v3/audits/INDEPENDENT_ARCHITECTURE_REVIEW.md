# V03 独立構造レビュー

2026年11月9日。対象は V03 の証明構造であり、既存の全補題の再発見・公刊原典の全面再査読・Lean 認証ではない。

## 判定

**PASS：証明構造を固定してよい。** 最終組立版を読解し、下記の量化・接続・全域 coverage・依存の除外を確認した。この点検で、未解決の数学的欠落、未処理のパラメータ領域、又は全 Betti 行への接続欠落は検出していない。

この判定は、公刊入力と明示された保存完全証明を前提とする構造の判定である。完成論文の外部査読済み、各公刊入力の再証明済み、又は Lean kernel による形式認証済みという判定ではない。

## 対象と方法

ユーザー仕様、五つの執筆断片、組立後の [骨子](../P14_PROOF_SKELETON_V03_JA.md)、[依存表](../P14_DEPENDENCY_MAP_V03.md)、[lemma registry](../lemma_registry.json)、[coverage](../COVERAGE_V03.json)、置換台帳、査読準備表を読んだ。特に V02 §16、§14.6 末尾の旧全域結論と、保持される局所証明の範囲を原文で区別した。

独立性は、別担当による今回の構造読解と registry からの独自の到達性・循環検査という意味である。以前の監査報告の結論を全体保証として代用していない。新たな数学探索、旧証書の再実行、scalar・幅 checker の反復実行は行っていない。

## 四つの橋

| 橋 | 最終版で確認した接続 | 判定 |
|---|---|---|
| A：jump strata → Tor | O2 は同 jump の strata だけの同型。O10 の connecting rank と補数はともに非負。O11 は実際の後続微分 rank を保持し、O12 の三段鎖から O6 の塔を望遠和にする。T と N 全体を同型としない。 | 接続を明示 |
| B：relative Tor → actual ordinary target | O14 は第0 homology の正確な補正 f+1 を引く。O15 は target 差の係数 R_j を恒等式で与え、全 j≤r の十分条件と余る非負係数を説明する。 | 全行への接続を明示 |
| C：carry 相殺 | IV.14 の Σκ_s≥m、j=1 の置換 r↦s_r、Σc_r=m を IV.15 の三行鎖で接続する。actual 核は M_s∩T_s のままで、socle 単射から R≤W−u を得る。 | 相殺を明示 |
| D：幅4 | V.24 は K′ と L′ の両座標を解き、非負条件の必要十分性を示す。制限 anchor も含めて全競合を尽くし、V.25 と κ_j の単調性から j=1 の正確な閾値へ進む。生存標準語の独立性から in(I_G)=J を示している。 | 全 m の証明を明示 |

E_TRANSFER は Q_C→Q_G の核長 P_C−P_G を Tor 長完全列で補償してから端点 spectral sequence を用いる。P_C=P_G、商の無条件 Betti 単調性、spectral sequence の退化のいずれも仮定しない。

## 量化と全域 coverage

| 領域又は境界 | 確認した処理 |
|---|---|
| 主定理 | 真正な最小生成系を持つ全数値半群、任意体、全 i≥0。source と completion はそれぞれ独自の最小多項式表示で Betti 数を取る。 |
| e=1,2,3 | I_BASE、I_THREE。e=1 に空集合の gcd を適用しない。三生成元では公刊入力の理想から商への添字換算を行う。 |
| ordinary と narrow の境界 | w≥m−1 と w≤m−2 が整数幅を排他的に全て覆い、w=m−1 は ordinary。 |
| ordinary の資源 | 同一の actual source・同一体・一つの cut から得る H_t だけを使用。δ=0 は空塔・零資源として O_LOW に含める。 |
| ordinary の全 cut | r=2,3 は O_LOW、r=4,…,8 は O_SMALL、r≥9 は O_LARGE。r≥3 の時だけ a≥a_r を用いる。 |
| Sidon の範囲 | actual numerical Apéry quotient の q_2=binom(e,2) が前提。cut から最大二次層を導く系には r=e−1 かつ r≥3 が必要。r=2 の反例と適用禁止が明記されている。 |
| small scalar の無限範囲 | 五行表と整数 s,t≥0 の O20 を保持し、r=6,7,8 の負の角だけを actual Sidon で排除する。有限点の回帰から全域へ外挿していない。 |
| narrow の正規化 | d≥1、u≥e−1、gcd 条件、m≥du+2 を保持。source の生成元を別の正規化半群へ置換しない。target は物理幅 du の actual completion。 |
| e≥6 | u=e−1,e は W_EDGE、e+1≤u≤2e−3 は W_DENSE、u≥2e−2 は W_SPARSE。隣接する全幅を覆う。 |
| e=5 | u=4,5 は W_EDGE、u=6,7 と u≥8 の二構造は W_FIVE。u=7 の整数改善は R>0 の分岐だけで用いる。 |
| N4 第一行 | u=3,4 は N_SMALL と N_WIDTH4、u=5 と u≥9 は N_FIRST、u=6,7,8 は明示した N_SMALL の紙上場合分け。 |
| N4 u=3 | d=1 は source=target、d≥2 は物理 target 幅 V≥6 を使用。 |
| N4 u=4,d=1 | 非境界対を N_SMALL、(a,b)=(1,3) の全 m≥6 を N_WIDTH4 の m=6 と四剰余で処理。 |
| 全高次行と上端 | N_HIGH は全 u の第2–4行を保持。W_SPARSE の V.14 は i=e まで、W_FIVE は第5行まで含む。ordinary は relative top j=r と O14–O15 による全行を含む。第0行は双方1、i>e は source が0。 |
| 任意体 | 一般 cut だけは同標数の無限純超越拡大と flat base change。狭幅は与えられた体上の複体と整数の単位 minor を用いる。有理重みは体内の除法ではなく数値不等式。異標数間の rank 一致を仮定しない。 |

## 依存 graph の独立点検

最終組立 registry の I_MAIN を始点として depends_on を再帰的に読んだ。

- 50 頂点、128 辺。ID の重複と未定義の依存先はともに0。
- 全50頂点が I_MAIN から到達可能。循環は0。
- 全頂点に statement、quantifiers、assumptions、depends_on、proof_core、sources、kind、characteristic、audit がある。
- E_ROW は W_SPARSE から、二変数 downset の入力 E_TWO は N_DISTANCE・N_WORDS から明示的に到達する。
- 旧 §15、196組証書、Navi 増分ルートを前提とする頂点はない。推移的に重なる直接辺は局所使用を示す表記であり、別の数学的仮定を加えない。

この有限 graph 検査は、記録された推論の構造を検査するものであり、補題自体を数学的又は形式的に認証するものではない。

## 指摘と解消

| 指摘 | 種別 | 最終組立版で確認した解消 |
|---|---|---|
| X_AP_BETTI の量化が interval d=1 に狭く、W_EDGE の d≥2 の算術列 source と不一致 | 公刊入力の scope 誤記 | X_AP_BETTI と X_AP_CONE を真正な算術列 <m,m+d,…,m+vd>、d≥1、gcd(m,d)=1 に修正。W_EDGE に両入力の辺を明示。 |
| N_DISTANCE・N_WORDS の二変数単項式 downset の根拠が graph に明示されていない | 依存記録の不足 | 両頂点に E_TWO の直接辺を追加。 |
| 全行 package E_ROW が主定理から未到達となる初期 registry | 構造記録の不足 | W_SPARSE に E_ROW の辺を追加し、到達性を独立確認。 |
| V02 §16 と §14.6 末尾の旧結論を広い出典参照から持ち込むおそれ | 出典引用の scope | I_MAIN は V03 Part VI を出典とする。I_PARTITION は旧整数幅分割だけ、N_WIDTH4 は N23–N28・m=6・全四剰余の局所証明だけと source_scope を明示。台帳と依存表も旧全域結論を継承しないと明記。 |
| 検算コード・監査報告・今回の骨子まで一律に「完全証明の所在」と表示する初期生成表 | 証拠種別の表示 | 最終依存表で紙上証明、公刊入力の記載、可読性・独立監査、厳密算術の補助検算、今回の骨子・合成を区別した。 |

上記は構造化の過程で修正された scope・依存・表示の問題であり、保存された数学的証明の破綻として報告するものではない。**未解決の指摘は0。**

## 保持する外部入力と残る監査境界

Green、必要箇所の BHP/EK、Kneser、算術列の Betti 公式と接錐一致、Lan–Tu–Vu の三生成元比較、Savchev–Chen を公刊入力として保持する。Koszul/Tor、Hilbert syzygy、rank Euler、有界 spectral sequence、Gröbner 除法は通常の基礎代数として区別されている。

旧 ordinary の first-hit・truncated lex・83組・665比較・5 tail は主ルートから外れる。BHP/EK 自体は狭幅 dense のため残る。N4 の196組証書は外れるが、Kneser、Savchev–Chen、actual 核補償、幅6–8の有限紙上場合分け、幅4の全 multiplicity、全高次行は残る。Navi は独立代替資料として保存され、主定理に二重に組み込まれていない。

残る仕事は、査読準備表に列挙された外部数学者による共通基礎・公刊入力の照合、保持証明をこの順序へ統合する全文執筆、及び実質的な Lean 形式化である。これらの未実施と、今回の構造内に未解決の数学的欠落を検出したこととは区別する。
