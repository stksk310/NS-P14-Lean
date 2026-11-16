# V03 から完全 Lean 証明へ：モジュール分割案

2026年11月9日（JST）。計画専用。基準は `proof_structure_v3/lemma_registry.json` の全50 ID、
`P14_PROOF_SKELETON_V03_JA.md`、`P14_REFEREE_READINESS_V03.md`。
監査対象の証明・コード・証書は変更しない。Lean のインストール・実装は行っていない。

この文書の工数は、経験のある Lean 数学者1人が AI を併用し、共通の固定 mathlib
を使う場合の**実働人日**である。10人日を2作業週とする。各区間は大きな不確実性を持つ
企画用の幅であり、納期の約束や統計的な信頼区間ではない。後続モジュールの工数は、
表に挙げた前提モジュールの輸出定理が既に完成している場合の**追加工数**である。
前提の数学を未証明のまま置いてよい、という意味ではない。

ライブラリの公開ソース調査はP14_LEAN_LIBRARY_AUDIT.mdに記録した。まだ適用のコンパイル検証はしていないため、
以下の範囲を校正前の追加工数として維持する。総工数と暦期間の扱いは主計画書に従う。各モジュールの範囲には、statement の型付け、
本文の証明、必要な局所補題、意味の接続、ビルドと独立した statement review を含む。
一般用途の API 整備を無制限に行う費用、数学的な欠落が新たに見つかった場合の研究、
別の証明ルートの探索、並行作業の調整・休暇・待機は別である。

## 1. 完成とは何を指すか

最後の定理は任意の体 `k`、真正な最小生成系を持つ全数値半群 `Γ`、全 `i : ℕ` について、
同じ `Γ` の actual tangent cone と actual interval completion の Betti 比較を述べる。
source と target の多項式環は、それぞれの最小生成系に対応させる。

各 ID は次の三段階を区別する。

1. **statement 完了**：量化範囲・次数・有限性・最小生成系・同じ体を型に表し、
   本文との照合が終わる。型だけがコンパイルしても proof 完了ではない。
2. **局所 proof 完了**：必要な補題を kernel が検査する。ただし未完の数学的前提を
   引数として受ける暫定 theorem は、条件付き成果物として明記する。
3. **意味の接続完了**：actual objects から前提の全証明を供給し、最終依存閉包に
   `sorry`、`sorryAx`、プロジェクト固有の未証明数学 `axiom` がないことを調べる。
   標準の Lean 論理基盤と、公刊数学を新しい公理として追加することは区別する。

全50 ID、下記の基礎追加物、公刊7入力のすべてが第3段階まで閉じて初めて
「完全 Lean 証明」と数える。監査 PASS、出典の存在、有限 checker の PASS、
主定理の型、前提付き主定理のビルドはその代わりにならない。

## 2. 先に固定する共通インターフェース

### 2.1 数値半群と actual cone

- `NumericalSemigroupData`：`Γ ⊆ ℕ`、加法閉性、有限補集合、昇順の真正な最小生成系、
  `m,e,w`。`e=1` を独立に扱い、空集合 gcd を狭幅正規化へ渡さない。
- `ordΓ(n)`：所属要素の生成元表示の**最大**長。最大の存在、有限性、表現との対応を証明する。
- `ActualCone k Γ`：本稿の `gr_𝔪 k[[t^Γ]]` と同一視できる構成。
  半群環や数値基底による実装を選ぶ場合、完成局所半群環の associated graded との
  graded algebra equivalence を別途証明する。単に同名を付けない。
- `coneBasis`：`n ∈ Γ` に対応する元は次数 `ordΓ(n)` にあり、積は order が加法的なときだけ
  数値指数の和となり、それ以外は0となる。このモデルと associated graded の同値を輸出する。
- `minimalPresentation`：`MvPolynomial (Fin e) k →ₐ[k] ActualCone k Γ` の全射、
  一次関係がないこと、各変数と指定された最小生成元の対応。
- `actualCompletion Γ`：`⟨m,m+1,…,g_e⟩` を実際に作り、atom が
  `m,…,m+min(w,m−1)` と正確に一致することを証明する。

### 2.2 Betti・Tor・有限次元

実装の第一候補は、実際の最小表示の変数列に関する Koszul homology の次元で Betti を
計算し、それが通常の多項式環上の `Tor` の次元であることを証明する方式とする。
導来圏全体の整備を最初の納品にせず、必要な解消・比較定理に範囲を絞る。

- `betti k Γ i` は source の `e` 変数、target は target 自身の変数で定義する。
- 関連 homology の `FiniteDimensional` または有限生成性からの有限性証明を先に与えてから
  `finrank` を使う。無限次元で `finrank = 0` となる定義上の挙動を消滅証明に利用しない。
- graded 各成分の有限次元性、total homology の有限台、次数和と total dimension の一致を証明する。
  Koszul の chain group は `G` を含み、体上無限次元になり得る。chain group 全体を
  有限次元と仮定して二重複体の評価を済ませない。
- `β₀=1`、source の `i>e` における消滅、理想/商の正行の添字換算を共通 theorem にする。
- `c_j^R` は環 `R` を型または明示引数で持たせる。交代和の非負性は rank/Euler の証明から得る。
- bounded な2行・3行二重複体の必要な次元不等式を、有限 filtration の部分商と rank の式から
  直接証明してよい。その場合も収束・端の添字・homology の有限性を証明する。
  「spectral sequence が退化する」という数学的仮定には置き換えない。
- 同標数体拡大の base change は、Koszul complex の tensor と homology、または flat resolution
  から証明する。一般 cut 用に無限純超越拡大を構成し、最後に intrinsic Betti に戻す。

### 2.3 有限組合せと整数・有理数

`Finset`/`Fintype` の剰余、語、downset、antichain、単項式、有限台の数列を共通語彙にする。
下添字が範囲外の二項係数、`ℕ` の切断減算と整数減算、ceil/floor、mod、gcd を明確に変換する。
有理重みの議論は `ℚ` または `ℝ` 上の数値不等式で行い、任意標数の係数体内部で
`1/(t+j)` を作らない。単位 minor の非零性は `±1` によって各体で直接証明する。

`OrdinaryWitness Γ k cut` に一つの cut と actual tower・資源列の由来を保持する。
`EndpointWitness Γ k norm` に元の source、正規化整数、actual 写像と核を保持する。
抽象的な scalar 補題を先に証明してよいが、異なる cut の cap や仮想正規化 source を
混ぜた入力を final theorem へ渡さない設計にする。

## 3. 全18モジュールと概算

`IDなし` は registry 外の必要な基礎追加物である。`X_BASIC` は M03 が一次責任を持つが、
数値的な前提は M01–M02、Gröbner 部分は M04 が供給する。`X_BASIC` という一個の
万能な仮定を宣言する設計は採らない。

| Module | 一次所有する registry ID | 追加実働人日 | 前提モジュール・輸出物 |
|---|---|---:|---|
| M01 数値半群・有限組合せ基盤 | IDなし：50 IDの外にある必須基礎 | 35–90 | 固定 Lean/mathlib の基本代数・有限集合 API |
| M02 actual tangent cone・最小表示 | IDなし：50 IDの外にある必須基礎 | 50–140 | M01 |
| M03 graded Koszul/Tor・必要な同調代数 | `X_BASIC`, `I_FIELD` | 100–280 | M01、M04 の Gröbner 輸出は該当 subpackage のみ |
| M04 初期加群・Gröbner・標準単項式 | IDなし：`X_BASIC` の Gröbner 部分を供給 | 50–150 | M01、基本多項式・加群 API |
| M05 算術列の全証明・actual target | `X_AP_BETTI`, `X_AP_CONE`, `I_TARGET` | 80–220 | M01–M04 |
| M06 三生成元の公刊比較 | `X_LTV`, `I_THREE` | 60–180 | M01–M04、M05 の target interface |
| M07 Kneser・長零和自由列 | `X_KNESER`, `X_SC` | 70–200 | M01 の有限群・語・計数 interface |
| M08 Green・Hilbert restriction | `X_GREEN` | 70–220 | M03–M04、generic linear form と体拡大 |
| M09 BHP/Pardue・Eliahou–Kervaire | `X_BHP_EK` | 100–300 | M03–M04、M08 の Hilbert/Macaulay 補助 API のみ |
| M10 ordinary の actual 座標・一つの cut・塔 | `O_COORD`, `O_CUT`, `O_VOLUME`, `O_TOWER`, `O_SIDON` | 55–140 | M01–M03、M08 |
| M11 harmonic rank・Tor 鎖・target 係数 | `O_HARMONIC`, `O_TOR`, `O_TARGET` | 50–140 | M03–M05、M10 |
| M12 ordinary の scalar と全域閉鎖 | `O_LOW`, `O_SCALAR`, `O_SMALL`, `O_LARGE`, `O_CLOSE` | 25–65 | M05、M10–M11、M03 の base change |
| M13 狭幅正規化・端点 core から actual 核 | `I_NORMALIZE`, `E_CORE`, `E_COORD`, `E_KERNEL`, `E_STOP`, `E_BOUNDS` | 45–120 | M01–M04 |
| M14 Artin/Koszul 計数と actual Betti 移行 | `E_ARTIN`, `E_HOMOLOGY`, `E_TRANSFER`, `E_ROW`, `E_TWO` | 25–70 | M03–M04、M13 |
| M15 五生成元以上の全幅 | `W_EDGE`, `W_DENSE`, `W_SPARSE`, `W_FIVE`, `W_CLOSE` | 45–130 | M05、M07、M09、M13–M14 |
| M16 N4 の距離・標準語・第一行・高次行 | `N_DISTANCE`, `N_WORDS`, `N_HIGH`, `N_FIRST`, `N_SMALL` | 30–85 | M05、M07、M13–M14 |
| M17 幅4の全 m と N4 閉鎖 | `N_WIDTH4`, `N_CLOSE` | 20–65 | M02–M05、M13、M16 |
| M18 小生成元・分割・主定理 | `I_BASE`, `I_PARTITION`, `I_MAIN` | 8–25 | M01–M06、M12–M13、M15、M17 |

同じ基礎作業を後続モジュールの各工数に重複計上しない。例えば M12 の25–65人日は
一般 Green や Tor を新規に開発する時間を含まず、M08・M03 はそれぞれ別に必要である。
M05–M09 の工数は公刊定理の証明まで含む。文献 statement の包みを作るだけの工数ではない。
M08 の Hilbert/Macaulay 補助部と M09 の間の辺は API 再利用であり、BHP が Green を
数学的に前提にするという主張ではない。必要ならその補助部を独立ファイルに切り出す。

## 4. 各モジュールの具体的な仕事と受入条件

### M01 数値半群・有限組合せ基盤（35–90人日）

有限補集合の加法部分モノイドと有限真正最小生成系の表現を接続する。multiplicity、
embedding dimension、Apéry 元の各剰余での一意性、最大表示長、gcd と生成性を整える。
語の prefix、剰余 walk、有限 downset、各種 tail sum と二項係数の共通補題を作る。
正規化に必要な gcd、`q+1≤u`、`m≥du+2` の数値補題を整える。
registry の `I_NORMALIZE` 自体は `X_BASIC` への辺を保つため M13 が一次所有し、source は取り替えない。

受入条件：`Γ` と正規化整数の証明付きデータを返し、元の `Γ` の生成元について
必要な等式・最小性が輸出される。数値半群の抽象定義と有限生成元リストが別物のまま残らない。
最大の不確実性は、使用予定の最小生成系・Apéry API がライブラリにどれだけあるか。

### M02 actual tangent cone・最小表示（50–140人日）

`k[[t^Γ]]`、その極大イデアルと冪 filtration、associated graded を定義または再利用する。
数値基底モデルとの同値、order の積の法則、最小多項式表示を証明する。
半群環 `k[Γ]`、その局所化、完成、具体的な support 制限付き冪級数を使ういずれの選択でも、
本稿の actual cone との canonical な同値を輸出する。actual completion とその最小生成系もここで作る。

受入条件：ordinary の `G,A,T,N`、narrow の `C→G`、最終 Betti の `G` が同じ値または
明示した同値でつながる。associated graded の一般ライブラリがあっても、この同値の費用は消えない。
registry の50 IDにはこの construction 一式に対応する単独 ID がないため、独立した工数枠とする。

### M03 graded Koszul/Tor・必要な同調代数（100–280人日）

最初の下位成果は Koszul chain、homology、有限性、短完全列の接続写像と次元の式である。
次に polynomial ring の変数 Koszul が `k` を解消することと Tor 計算の一致、
graded/total Betti、Euler/rank、必要な vanishing、体拡大の不変性を閉じる。
最後に2行・3行二重複体の bounded filtration と homology 次元評価を整える。
一般 spectral sequence を丸ごと実装する代わりに必要な有限段の rank 式を証明してよい。

受入条件：`I_FIELD`、完全列での Tor 不等式、各 `c_j` の意味、endpoint の三項 Euler、
ordinary/endpoint の二重複体評価が actual modules に使用できる。
同じ標数の拡大のみを用いる。M04 が供給する Gröbner 基礎も含め、`X_BASIC` の本稿で使う
各項目を証明済み theorem へ解体し、抽象 `X_BASIC` 仮定を残さない。

このモジュールは「標準的だから数日」と見積もれない。既存の complex/Tor があっても、
graded 有限性、指定した変数列、minimal-presentation convention、自然性の接続が必要になる。

### M04 初期加群・Gröbner・標準単項式（50–150人日）

単項式順序とその well-foundedness、同次除算、initial ideal/module、標準単項式の基底、
初項による generator 数の上界を整える。任意係数体、有限自由加群、指定した多変数順序に対応させる。
M11 の初項加群への行列 rank 比較、M14 の親子計数、M17 の特殊な重み順序で使う定理を別に輸出する。

受入条件：monomial generator を数えるだけでなく元の ideal への停止除算を証明でき、
initial ideal の包含から等号へ進む際に標準単項式の独立性を明示できる。
一般 Gröbner API の有無と graded module 版の不足で幅が大きく変わる。

### M05 算術列の全証明・actual target（80–220人日）

`X_AP_BETTI` の真正な最小算術列について、出典の自由解消または同値な Koszul 計算を形式化し、
exactness と各 rank を証明する。単に formula を宣言しない。
`X_AP_CONE` は semi-group ring と tangent cone の Betti 一致を、原典の仮定に沿って証明する。
その後 actual interval の atom、剰余パラメータ `D`、TAR/TMIN、幅方向の単調性を `I_TARGET` にまとめる。

受入条件：任意体、全行、範囲外の0、source の完全算術列にも使える一般性がそろう。
target 側だけの `d=1` の式では `W_EDGE` の完全算術列 source の依存を満たさない。
工数の主因は公刊公式と cone 一致の閉じた証明で、代入算術は後半の一部である。

### M06 三生成元の公刊比較（60–180人日）

Lan–Tu–Vu Theorem 1.1 の使用範囲を正確に型にし、証明に必要な三生成元 defining ideal、
接錐の場合分けと Betti 計算を閉じる。原典の ideal Betti convention から quotient へ
添字を変換し、`I_THREE` の全行・任意体・actual completion を得る。

受入条件：`X_LTV` 自身が形式的な定理であり、「引用したので仮定する」という引数が残らない。
source/target の同一化、最小表示、0行、高次消滅まで含める。
原典の補題群の再利用状況をまだ確認していないため、公刊 theorem の wrapper 程度の見積りにはしない。

### M07 Kneser・長零和自由列（70–200人日）

有限 Abel 群の sumset、stabilizer、商群と cardinality を接続して Kneser を証明する。
使用する反復版と、合成数位数の cyclic group への適用を含む。
Savchev–Chen は finite cyclic group の零和自由な**列**と、unit による移動後の
正の代表の和について、必要な長さ `>u/2` の定理を証明する。

受入条件：`X_KNESER` と `X_SC` は異なる公刊証明として閉じ、subset と multiset/sequence を
取り違えない。SC の unit を actual tangent cone の反転同値と読み替えない。
概算の内訳の目安は Kneser 35–95人日、SC 35–105人日で、共通 finite-group API の二重計上を避ける。

### M08 Green・Hilbert restriction（70–220人日）

Hilbert 関数、Macaulay 展開と下降、generic linear form の存在を整え、使用する Green の
次数2・任意標数の statement を証明する。原典の一般定理を全部形式化するか、必要な次数2の
証明に限定するかは原典確認後に決める。いずれも非空の条件集合と係数体の仮定を証明する。

受入条件：無限体上で一般 cut を選べることと、反復時の仮定を輸出する。
有限体への対応は M03 の純超越拡大を介して行う。M10 の `O_CUT` はこの定理から
同じ cut を一度作り、全高次の消滅まで導く。

### M09 BHP/Pardue・Eliahou–Kervaire（100–300人日）

同 Hilbert 関数の lex ideal の存在、任意標数での Betti dominance、安定/lex monomial ideal
の EK formula を必要な quotient convention で証明する。正標数を characteristic-zero の
generic-initial-ideal 性質だけで済ませない。全 Hilbert profile に対する一つの lex 商を使う。

受入条件：`X_BHP_EK` の両成分が形式的に証明され、M15 の dense 幅だけへ適用される。
旧 ordinary lex の証書経路を新たな前提にしない。ここは公刊7入力の中でも大きな開発リスクがあり、
EK の組合せ計算ができても BHP/Pardue の支配定理が自動的に得られるわけではない。

### M10 ordinary の actual 座標・一つの cut・塔（55–140人日）

M02 の basis から actual Apéry 商 `Q=A/N`、terminal/head、逆向き filtration、
**同 jump の strata のみ**の加群同型を証明する。least-offset path と最長 order の安定を証明し、
terminal jump の望遠和を作る。M08 と M03 から一つの square-zero cut を固定する。
その cut による tower の完全列、単一次数生成、有限な `H_t`、全 cap の共存を証明する。
最後に最大二次層から Sidon 差の単射を作り、実現不能な3つの角を排除する。

受入条件：`T≅N` という誤った全体同型に頼らず、同じ `Γ,k,cut` の証明付き資源一式を返す。
`δ=0` の空塔、`r=2` の範囲、`r≥3` の Sidon 使用条件、全端点を含める。
大きな局所モジュールなので、座標→path→cut→tower→Sidon の順に subpackage を区切る。

### M11 harmonic rank・Tor 鎖・target 係数（50–140人日）

`O_HARMONIC` では初期加群による block 三角 rank 比較と単位 minor を実際に構成する。
整数 rank に対する有理数平均を証明し、`c₀` と top rank を別に扱う。
`O_TOR` は strata の完全列を三段鎖へ写し、非負の減算補正を保持した後に不等式へ進む。
`O_TARGET` は zero-homology の正確な補正、係数畳み込み、`R_j−L_j` の margin を証明する。

受入条件：readiness A・B の式と添字が actual tower から final Betti に接続する。
spectral-sequence degeneration や任意商の Betti monotonicity を使わない。
`j=1` の minimal-generator 数と `j=r` の top relative rank を省略しない。

### M12 ordinary の scalar と全域閉鎖（25–65人日）

同じ有限資源列を引数とする数値 theorem として、`r=2,3` の直接評価、重みの scalar 化、
`r=4..8` の固定5行、`r≥9` の harmonic barrier と有限差分帰納を形式化する。
5行の有理定数は kernel が検査する等式・不等式にし、有限 checker の出力を仮定にしない。
3つの負基点を M10 の actual Sidon で排除し、M11 と体拡大の下降を接続する。

受入条件：`O_CLOSE` が全 actual ordinary source と全行を閉じる。
有限 anchor は普遍的な恒等式・単調性の証明の一部として使い、有限サンプルから無限範囲を推論しない。
この追加工数が比較的小さいのは M03・M08・M10・M11 が完成済みという条件による。

### M13 狭幅正規化・端点 core から actual 核（45–120人日）

M01 の数値補題と証明済み基礎を使って `I_NORMALIZE` を閉じる。
integer core の monomial algebra と actual `G` への写像を構成し、次数、全射、monomial kernel を証明する。
剰余別の有限二座標分解を作り、長い表示の全競合を `j≥1` で網羅する。
actual kernel を `M_s∩T_s` と同定し、有限停止と `v^m=0`、rank 0 を証明する。
socle 単射、carry 和、`Σκ_s≥m`、三行の評価を通して `R≤W−u` と height bound を得る。

受入条件：readiness C の全橋が閉じる。`T_s` をそのまま actual kernel として使わず、
短い側が core に属する条件を交差に残す。`gcd(m,u)=1` や Cohen–Macaulay 性を追加しない。
反転して得られた height を元の actual source の height と同一視しない。

### M14 Artin/Koszul 計数と actual Betti 移行（25–70人日）

Artin 商の初期 ideal に対する親子の重み付き計数、単位 minor による全高次行 bound を証明する。
endpoint homology を `(P_G,P_G+R,R)` と計算する。
`0→K→Q_C→Q_G→0` の Tor と actual double complex から、核長を補償して `P_G` を消去する。
一般 `q` の `E_ROW` と、二内部変数の `E_TWO` を計算する。

受入条件：`Q_C` と `Q_G` の差がゼロであるとは仮定せず、全行の補償式が actual `G` の Betti を拘束する。
二変数 `Q_C` の monomial 性、socle、Euler の適用条件も証明する。

### M15 五生成元以上の全幅（45–130人日）

`W_EDGE` は最小幅の AP source と一欠落幅の二つの構造、端の indicator を処理する。
`W_DENSE` は missing-prefix から資源を作り、一つの lex 商に BHP/EK を適用し、
親子の調和計数と target の係数差を閉じる。
`W_SPARSE` は composite order を含む Kneser の成長、距離和、多項式、全 row の幅方向単調性を証明する。
`W_FIVE` は幅6・7、`R>0` 条件付きの改善、antipodal quotient の同定、全高次行を処理する。

受入条件：`W_CLOSE` の隣接する幅区間が空隙なく全 `e≥5` を覆い、0行・top 行・消滅域を含む。
既存算術 checker の polynomial は仕様照合に使えるが、Lean の普遍証明へ変換する。
幅6・7の小表だけを認証して全幅完成とはしない。

### M16 N4 の距離・標準語・第一行・高次行（30–85人日）

Kneser の反復から三点集合の距離和を作り、socle antichain が full triangle を含むことを証明する。
SC の列を mixed standard word に適用し、元の向きの height と純軸・混合語の ceiling を得る。
三つの endpoint relation から禁制矩形を取り出し、その count と socle bound で無限第一行を閉じる。
幅6–8、幅3–4の紙上場合分け、高次3行の polynomial gap を証明する。

受入条件：`N_FIRST` の閉鎖域は `u=5` または `u≥9` に限って使い、残りを `N_SMALL` が埋める。
`N_SMALL` に残る `u=4,d=1,(a,b)=(1,3)` を M17 へ正確に渡す。
旧196行の exact-core 証書を前提に戻さない。

### M17 幅4の全 m と N4 閉鎖（20–65人日）

重み付き単項式順序、core の自由列・制限列、全長い表示の座標 `K′,L′`、正確な停止閾値を証明する。
禁制語の消滅と非禁制語の独立性を別に証明し、actual initial ideal の**等号**を得る。
停止除算から generator 数を得て、`m=6` と全 `m>6` の四剰余を比較する。
M16 の第一行・高次行と合わせて `N_CLOSE` を閉じる。

受入条件：readiness D の whole-`m` family が証明される。サンプルの有限 `m` 計算、
generator 数だけからの initial-ideal equality、正規化 target への取り替えは用いない。

### M18 小生成元・分割・主定理（8–25人日）

`e=1`、`e=2` の具体的な presentation と Betti、`e=3` の M06 の適用を接続する。
`e≥4` の整数幅分割、`e=4/e≥5`、ordinary の cut 範囲の全被覆を証明する。
actual completion の最小表示を固定したまま、M12・M15・M17 の theorem を合成する。

受入条件：主定理の実引数から全50 IDと基礎の証明へ到達し、mathlib 版と import 閉包が固定される。
最終依存に未証明の公刊 theorem、歴史的証書、条件付き placeholder が残っていないことを確認する。

## 5. 7つの公刊入力を消さない

| Registry ID | 一次所有 | 原典と使用範囲 | 完全 Lean に必要なもの |
|---|---|---|---|
| `X_GREEN` | M08 | Caviglia §1 (1.1) に再掲の Green、次数2・任意標数 | 必要な restriction theorem と一般形式の存在の証明。引用 statement のみでは不足 |
| `X_BHP_EK` | M09 | Juhnke-Kubitzke–Venturello §2.2 Lemmas 2–3、BHP/Pardue と EK | Betti dominance の任意標数版と lex の公式の両方。dense 幅だけに適用 |
| `X_KNESER` | M07 | DeVos Theorem 1 | finite Abel group の stabilizer bound と使用する反復版。素数位数だけでは不足 |
| `X_AP_BETTI` | M05 | Gimenez–Sengupta–Srinivasan Theorem 4.1 | 一般の真正最小算術列の exact Betti formula。target と `W_EDGE` source に適用 |
| `X_AP_CONE` | M05 | Herzog–Stamate Proposition 2.5 | 本稿の範囲で AP semigroup ring/cone の Betti 一致を証明 |
| `X_LTV` | M06 | Lan–Tu–Vu Theorem 1.1 | 三生成元の比較自体を形式化し、ideal/quotient 添字と actual completion を接続 |
| `X_SC` | M07 | Savchev–Chen §4 Theorem 8 | 長零和自由列の unit と代表和の結論まで証明。N4 の mixed 語への適用条件を確認 |

原典 locator は registry を採用した。ここで原典全体を新たに数学監査したとは主張しない。
使用する原典の補題依存が想定以上に大きければ、M05–M09 の上限を超える可能性がある。
各公刊入力に、型付き statement のみ／条件付き proof／閉じた proof の状態を別に記録する。

## 6. library reuse の現時点の区別

以下は担当モジュールの再利用を評価する区分である。具体的な公開ソース調査はP14_LEAN_LIBRARY_AUDIT.mdを参照。
ソース上で確認できた宣言と、今回の対象へコンパイルして適用できることを区別する。

- **再利用の基盤として既知の一般的分野**：Lean/mathlib の自然数・整数・有理数、有限集合、
  有限群、線形代数、polynomial、ideal/quotient、module/tensor、homological-complex の基礎。
  ただし、この区分は目的の定理や必要な graded API がそのままあるという主張ではない。
- **存在・適合を監査してから差し引く部分**：associated graded と completion の同値、
  多変数 graded Koszul/Tor の有限性と一致、短完全列の自然な接続、必要な filtered-complex bound、
  module Gröbner、generic cut と正標数、AP/LTV/Green/BHP/EK/Kneser/SC の該当 statement。
- **本稿固有として開発を予定する部分**：actual Apéry head/jump strata、単一 cut の tower と
  同一資源、harmonic block minor の接続、actual endpoint kernel と補償、幅4全 m の初期 ideal、
  新 ordinary 5行と N4 第一行の paper replacement、全領域の実引数による合成。

基盤の型が存在することと、必要な仮定・自然性・有限性を持つ theorem が存在することを分ける。
後者まで exact に確認された再利用だけ、担当モジュールの再見積りで差し引く。

## 7. 先に試す縦の一断面

**第一候補は `I_BASE` の二生成元ケースを actual objects から閉じることである。**
18モジュールの完了を待たず、M01–M04 の必要な小部分と M18 のこの場合だけを通す。

1. `Γ=⟨m,n⟩, m<n, gcd(m,n)=1` と最小性、actual completion を構成する。
2. actual completed-semigroup tangent cone から `k[x,y]/(y^m)` への同値を証明する。
3. 実際の2変数 Koszul homology、有限性、`β=(1,1,0,…)`、Tor convention を接続する。
4. actual target の最小多項式表示の非零関係から `β₁≥1`、`β₀=1` を証明し、
   source の高次0を使ってこの全行比較を閉じる。

この断面は M05 の大きな公刊 AP 公式を仮定せずに、source の意味、target の最小表示、
Betti の意味、finite-dimensionality、型の搬送の費用を実測できる。
実際の source を通らない scalar だけの試作より、全計画のリスクをよく測れる。
目安は共通基盤を利用できる場合で15–40人日、actual-cone bridge や Koszul API を広く作り直す
場合は40–100人日以上。これは M01–M04・M18 の部分工数であり、表に上乗せしない。

並行して着手しやすい小成果は M12 の5行有理 scalar と M16 の有限 downset 計数だが、
これらだけでは main theorem の actual connection を検証できない。
第一断面後に固定するのは、cone 表現、Betti 表現、必要な有限次元証明、graded/total 搬送の
4 interface と、その実績に基づく M01–M04 の再見積りである。

## 8. 依存の扱いと避けるべき完成判定

registry の直接辺は50頂点・128辺の数学的依存である。本計画はその頂点を一次所有先へ写す。
新しい foundation/API の辺を追加するが、別証明への数学的置換は提案しない。
M03 と M04 は共通 `X_BASIC` の別部分なので、M04 は M03 全体に依存しない。
M08 の Hilbert/Macaulay 補助部も M09 から独立して完成させ、モジュール循環を避ける。
`I_NORMALIZE→X_BASIC` の registry 辺を残したまま M03 が数値基盤を使えるように、
`I_NORMALIZE` は M01 でなく M13 が所有する。基礎 API とその後の定理の所有を分ける。

旧 ordinary 83-profile/665-comparison/5-tail、旧N4 196組、Navi 増分証明は主依存に戻さない。
5行の有理 anchor と幅6–8の少数の紙上場合分けは残るが、無限範囲の証明と接続して検査する。
最初から「全50 IDの theorem 宣言」「全7公刊 theorem の axiom」「最終 theorem の `by exact`」を
作っても、それは依存の展示であって本計画の完了ではない。

機械可読の一次割当てと registry 由来の module 辺は同じディレクトリの
`modules.json` に保存する。mapping は registry の全 ID と完全一致し、重複がなく、
quotient graph が非循環であることを検査する。これは計画の coverage 検査であり、数学や Lean proof の検査ではない。
