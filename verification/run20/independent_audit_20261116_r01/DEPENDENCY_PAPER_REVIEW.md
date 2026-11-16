# Run20 独立依存・原稿対応監査

対象: `/workspace/NS-P14-Lean-run18`、HEAD `a5e122a4d09536b1609c5faa8d419f8faf81671f`。2026-11-16 UTC。

判定: **PASS（以下に限定した静的な依存・原稿対応監査）**。読んだ範囲に、必要な公刊入力を未証明の引用axiom/比較certificateへ置換した箇所、元の量化を落とした主出口、不要化した強い結果を必要な形式化済み入力と誤表示した箇所は見つからなかった。新規findingsは Critical 0 / Important 0 / Minor 0。

これは主定理の全数学の再証明、全670 moduleの全proof termの独立精読、Lean kernel検証の再実行、全宣言collectAxiomsの独立実行、cold/ZIP/publication認証の判定ではない。これらをこのPASSで代替しない。

## 実施と証拠の境界

- 読取専用でGit HEAD、指定されたRun20の7文書、旧 `proof_structure_v3/lemma_registry.json`、V06全体・共通章・第6章・依存被覆と他章の関係箇所、下記Lean定義/証明本文を調べた。
- Pythonの標準ライブラリだけによる文字列照合で、50 IDについてID集合、`original_statement`、`original_quantifiers` が旧registryと全件一致することを確認した。status文字列や既存reviewのPASSをこの一致の根拠にしなかった。
- 各 `public import`/`import` を読み取った `NSP14.Main` のローカル静的import閉包は670 module。これは宣言単位のkernel依存閉包とは区別する。
- 同閉包のsourceを危険語 `axiom/sorry/admit/native_decide/unsafe` で走査し、非コメント行に該当する使用を見つけなかった。これは全公理閉包を実行検査したという主張ではない。
- V06の全7章の本文は、それぞれstripした文字列が全体 `NS_P14_SHARP_PROOF_JA.md` にそのまま含まれる。全体だけ別の定理へ変更されたという不一致はなかった。
- Lean/Lake/checker/packager、repo内のPython scriptは実行していない。repo/source/evidence/cacheへは書いていない。唯一の出力はこの `/tmp/run20-dependency-independent-audit.md`。

## 主出口と対象の意味

`NSP14/Main.lean:10` の実定理は引数 `S : NumericalSemigroup`、`k : Type`、`[Field k]`、`i : ℕ` のみ。比較結論や有限証書を引数へ入れていない。`Main/Branches.lean:10` の `IntervalComparison` は両側actual completed coneのBetti比較そのものであり、sourceとtargetは各自の `AtomExponent` / `FullPolynomialRing` を用いる。Mainの各枝は `Main.lean:20–25` で実proof出口を呼ぶ。

対象の定義も追跡した。

- `Semigroup/Basic.lean:12` は実際のcofinite additive submonoid of ℕ。任意の数値パラメータrecordをsemigroupと呼び替えたものではない。
- `Semigroup/FormalSemigroupRing.lean:16` は実Sにsupportを持つ `PowerSeries k` のsubalgebra。
- `Semigroup/FormalTangentAlgebra.lean:15–22,171` はその実maximal-ideal powersの商と直和。
- `Homological/Betti.lean:16–18` は有限生成polynomial moduleの実Koszul homologyのk次元。`KoszulTor.lean:47–51` は実free resolutionとtensor同型から `CategoryTheory.Tor` への同型を構成し、`Betti.lean:42–46` がそのcoefficient restrictionを与える。単なる数値profileの定義をTorと呼んでいない。
- `Homological/ActualTorTransport.lean:20–33` はfull atom presentation上の実Tor/Betti transport。`ActualKoszulTransport.lean:17–31` はfull変数とnon-x変数を別々に保持。
- `Semigroup/IntervalCompletionAll.lean:17–27` のtarget carrierは文字通り `closure (Icc multiplicity maxAtom)`。`Main/IntervalTarget.lean:10–26` は同carrierから双方のactual Bettiを移し、conductor witnessを同一視しない。e1のliteral [1,1] は同ファイル:28–32。

したがってV06共通章:5–18,48–101および第6章:48–51の「元のS・元の任意体・各自の最小表示・literal interval completion・全i」の意味は、調べた実出口と整合する。

## 七つの公刊入力を実consumerまで追った結果

引用文献の原典全文の独立査読はしていない。以下は引用と同じ名前のaxiomがあるかという検査だけではなく、必要な契約を実証明で供給しているかのsource追跡である。

| 入力 | 直接読んだ実proofとconsumerへの接続 | 結論・量化の評価 |
|---|---|---|
| Green | `Green/QuadraticRank.lean:20–92` → `HyperplaneStep.lean:32–54` → `HyperplaneFlag.lean:20–101` → `Semigroup/ActualGreen.lean:69–95` → actual cut | 次数2の必要特殊版。無限体上の一つのbilinear productと一つのindependent flagを構成する。alternating分岐もあり、char 2を除外しない。一般全次数Greenの形式化完了とは表示していない。 |
| BHP/EK | `Lex/GenericDistractionIteration.lean:144–169` → `BettiComparison.lean:12–27`、`StrongStableEK.lean:275–292` → `TotalBettiComparison.lean:12–29` → `Width/CoreLexPresentation.lean:33–63` → `DenseLexResources.lean:60`以降 → `DenseComparison.lean:16–38` | 任意Field。actual homogeneous quotientの全Hilbert関数を保持するlex商一つを構成し、そのactual graded/total Bettiを比較。generic stable comparisonの存在や同Hilbert性を未証明の前提として受け取っていない。 |
| Kneser | `Additive/KneserCore.lean:284`からのstrong-induction proof、`Kneser.lean:19–24` → `CyclicGrowth.lean` / `KneserIterated.lean` / `FourPointGrowth.lean:13–77` → `CyclicAntipodal.lean` → 幅の距離・分類 | finite nonempty setsとactual translation stabilizerのthickening版。合成数位数を許す。素数群に置換しない。採用sourceには著作権・Apache 2.0・出典が明記される。license bundleのbytes検査は担当外。 |
| AP Betti公式 | `ArithmeticSequence/ModelTorClosure.lean:14–47` → `BettiFormula.lean:34–81` → `Target/IntervalAPBetti` / `IntervalBetti` とfull AP枝 | actual kernel inclusionのTor map vanishingを変数倍へのfactorizationから証明しLESへ供給する。単に数式profileを定義しただけではない。`Source.lean:10–18` はm≥2,d≥1,v≥1,v<m,gcd(m,d)=1で、d=1へ限定しない。正行、0行、completed版がある。 |
| AP cone一致 | `ArithmeticSequence/ConeBetti.lean:11–62`、特に `semigroup_cone_totalBetti` → `BettiFormula.lean:51–81` | 実semigroup quotientとactual headのpolynomial-module iso、実regular-element reduction、actual x-regularityによる比較。半群環とconeそのものを同一環と仮定していない。 |
| LTV比較 | `SmallEmbedding/ThreeComparison.lean:184–238`、`LanTuVu.lean` のone-letter資源、`ThreePresentation.lean` のactual source/endpoint構成 → Main e3 | 同じ全幅・全行比較を十分な別証明で与える。広幅はactual ordinary closure、狭幅u=2はactual AP、u≥3はone-letter endpointから支払う。追加の強い三線形上界を形式化済みとは主張しない。 |
| Savchev–Chen | `Additive/SavchevChen.lean:12–71` のconnected representatives経由の証明 → `TwoValueSequence` / `StandardWordSequence` → `NarrowFour/StandardWords.lean:42–164` | 一つのactual unit cとNatの代表総和<uを結論する。mod uでの和だけで置換しない。SCを仮定recordで受け取らない。unit正規化を数値半群の同型とみなさず、元offsetの整数関係へ戻して標準語を排除する。 |

任意標数から元の体への復帰は、APでは `BettiFormula.lean:45–47`、ordinaryでは `Ordinary/NumericalBettiClosure.lean:68–77` に明示される。いずれも `Homological/ActualCoefficientBaseChange.lean:196–200` の元のactual Gの全行Betti一致を使う。char 0へ変更してBetti/rankが同じだと仮定する箇所は、この経路に見つからない。

X_BASICについては、通常Tor/Koszul同型に加えて、実exact sequence、有限homology、rank Euler、標準単項式・minor経路を必要なconsumerに供給する設計を確認した。一般spectral sequenceや一般Hilbert syzygyの全百科事典的形を実証明したとの主張としては読まない。必要上方消滅は実Koszul複体の長さから `Betti.lean:20–25` で供給される。

## V06の端点核心

1. **全j実核**: `Endpoint/ActualKernel.lean:10–17` は全 `j : ℕ, 1≤j` と全core点の競合を定義する。:24–82でactual numerical orderによる死点と同値、:86–93で `actualDeadFiber = coreFiber ∩ competitorFiber`。競合領域だけをkernelと置いていない。V06端点章:71–120と対応する。
2. **元のR/Hx**: `ArtinQuotient.lean:60–62` のactualP/coreP/actualR、`Socle.lean:14–15,48–61` の元のGの同時annihilatorとの同型を読んだ。`SocleBounds.lean:23–50` は同じDのactualRを同じDのwordVolume/coreHeightで抑える。`CompetitorBounds.lean:49–74` は全jの直接高さで、停止回数を前提としない。reflected coreのheightを無条件に代入する経路は見つからなかった。
3. **PC/PG補償**: `Compensation.lean:17–49` はactual `QCoreToActualModule` のkernelと短完全列、:57–76でその長さがPC−PG、:84–102で実LESと有限kernel chain boundによる補償。`FullTransfer.lean:14–43` が補償をmergeし、:54–64でβ(q+2)≤actualRと上方消滅を別に保持する。PG≤PCだけを使った不正なBetti単調性ではない。
4. **HxとSC復帰**: `NarrowFour/StandardWords.lean:94–115,119–164` は二つのlabel順序をどちらも元offset関係へ戻す。:181–219で元DのcoreHeight≤u−3とsmall actualR=0。`SocleTriangle.lean:104–140` はsocle個数からtriangle全体の包含を証明しており、単なる数値のtriangle-card仮定ではない。
5. **N4 cubic**: `NarrowFour/CubicPayment.lean:35–47` の式は正確に `4z^3+45z^2+140z+36`。`HigherRows.lean:186–234` はu3/u4/u5/u≥6を分け、u≥6だけ新cubic側へ渡し、i=4も処理する。旧quartic/quinticの支払いを必要入力へ戻していない。
6. **幅4全m/全j**: `WidthFourCompetitors.lean:69–103` はL′とK′の両制約を保ったままdelta<0を証明し、:119–127で全jからj1 thresholdを導出。:157–168はrestricted competitorの不可能性を証明し、:178以降はactual numerical orderへの同値。`WidthFourInitial.lean:379–421` のlive像単射→actual kernel equality→actual presentation、:469–479のactual第一Torと生成元数、`WidthFourComparison.lean:283–357` のm6および全四剰余6/8/8/6の支払いまで追った。mやjの有限上限を仮定する証書ではない。

## 各枝と旧50 IDの扱い

- e1/e2: `SmallEmbedding/Base.lean:81–89,152–187`。e1はliteral carrier equality、e2はactual二原子APのBetti列(1,1,0,…)を証明してactual target第一行へ接続する。旧具体的presentation `k[x,y]/(y^m)` 自体を追加の形式化完了義務として数えないことは台帳で明示される。
- e3: 上のLTV代替証明。`three_comparison` の出口にはhe=3以外の数学的比較前提がない。
- ordinary: `ActualWitness.lean:10–17,21–36` は元sourceと一つの実cutを構成し、`Semigroup/ActualResources.lean:11–65` が同sourceのactualLayersからresource recordを証明する。`ActualTorRow.lean:24–48` のactual R-Tor→resource→target、`RelativeRowsAll.lean:11–41` のH0/terminal/全正行、`NumericalBettiClosure.lean:15–77` のH0 correctionと元の体への復帰、`Closure.lean:16–27` のactual completionを追った。`NumericalClosure.lean:109–153` はr2をtriangular仮定なしで扱い、r3とr4..8/r≥9を別処理する。数値recordだけのclosure theoremをMainから直接仮定していない。
- e4 narrow: `NarrowFour/Comparison.lean:30–78` は全物理狭幅。高次と第一行を分け、u5/≥9、幅4の最後の族、残る小幅へ網羅的に進む。
- e≥5 narrow: `Width/Closure.lean:16–38`、`FiveComparison.lean:13–33`、`DenseComparison.lean:16–80`、`SparseComparison.lean:10–48`。full AP/one-hole、dense t2とt≥3、sparse、五生成元u4/u5/u6,7/u≥8のactual枝を保持する。physical幅duからactual targetへのcapacityを使い、最小AP d1はcarrier equalityを用いる。

50 IDの内訳は、共通/合成 `X_BASIC,I_NORMALIZE,I_PARTITION,I_BASE,X_LTV,I_THREE,I_FIELD,X_AP_BETTI,X_AP_CONE,I_TARGET,I_MAIN`、ordinary `O_COORD,X_GREEN,O_CUT,O_VOLUME,O_TOWER,O_HARMONIC,O_TOR,O_TARGET,O_LOW,O_SCALAR,O_SIDON,O_SMALL,O_LARGE,O_CLOSE`、端点 `E_CORE,E_COORD,E_KERNEL,E_STOP,E_BOUNDS,E_HOMOLOGY,E_TRANSFER,E_ARTIN,E_ROW,E_TWO`、幅 `W_EDGE,X_BHP_EK,W_DENSE,X_KNESER,W_SPARSE,W_FIVE,W_CLOSE`、N4 `N_DISTANCE,X_SC,N_WORDS,N_HIGH,N_FIRST,N_SMALL,N_WIDTH4,N_CLOSE` で、重複/欠落なし。各JSON entryは原文/量化を残す一方、必要契約/十分な代替/歴史的結果を区別する。

特に `N_FIRST` のstatusは `PROVED_V06_CONTRACT`。実 `FirstCount.lean:148–214` のguard `k0≤h` 付き除去三角形とV06 N5に対応し、省略条件を無条件な強化へ読み替えない。この点も「全50 IDのあらゆる原文の強化を同じ形式で証明した」という意味のCOMPLETEではない。

## 不要な強い結果と主依存への再流入

静的Main import閉包に `Endpoint.Stopping`、`Width.AntipodalBasis/Presentation/Ideal/Volume` はない。旧83 profile/665比較/5tail、196 core証書、Navi増分に該当するmodule/cache/certificate importも見つからない。

一方 `ArithmeticSequence.ProfileBounds` と `Lex.FiniteHilbertProfiles` はimportされる。これらの名前を旧profile証書と混同しない。前者は実AP公式の数値下界、後者は全Hilbert関数を固定した単項式profileの一般的有限性/安定化の証明（`FiniteHilbertProfiles.lean:10–63`、`GenericDistractionIteration.lean:144–169`）であり、固定有限ケース表の証書ではない。

`RUN20_DEPENDENCY_COVERAGE.json` に列挙される全moduleがMainの最小依存であるとは限らない。例えば歴史的 `E_STOP` のStopping、`FiniteSocleBounds`、`ThreePointGrowth`、`RowPackage` はMain import閉包外である。JSONは「実proof群とconsumer対応の索引」として読み、これらの列挙をMainに必要な未証明前提がある/ないという証明には使わなかった。

未形式化または主張対象外の強さとして、一般全次数Green、LTVの追加三線形上界、任意presentationに対する一般initial-ideal等式、旧N4 quartic/quintic支払い、普遍的exact antipodal b1=h+4を挙げる台帳の扱いは適切。antipodal第一行の実consumer `AntipodalComparison.lean:74–112` は候補語spanning上界・一般harmonic・actual R bound・整数支払いを使い、exact presentation/体積/第一Betti等式を前提にしない。歴史的Stoppingの強い周期停止結果は保存されるがMainの必要入力にはなっていない。

## 完成主張への評価

指定7文書を突き合わせたところ、`PAPER_CORRESPONDENCE` は必要数学の接続を主張し、`UNPROVED_DECLARATIONS` は必要数学上の未証明宣言なしと述べつつ公開COMPLETEと分離する。`FINAL_REVIEW_JA.md:3–7`、`HANDOFF_JA.md:8,18` もsource-boundの説明文だけをCOMPLETEの証拠としない。`EXECUTION_LEDGER` のbuild/fixture/型監査PASSの既存記述は今回の数学的接続判定の根拠に使用しなかった。

この独立監査範囲では、必要な七公刊入力と共通代数を引用axiom/conditional certificateのまま残して「全P14完成」と呼ぶgap、任意標数/actual Tor/全j kernel/PC−PG補償を落とすgap、または不要強化を形式化済み必要入力として数え直す過大表示は検出していない。全P14完成の最終判定には、別担当のMain数学監査と固定sourceに束縛されたcold実行・型/公理監査・bundle/publication認証を合わせる必要がある。
