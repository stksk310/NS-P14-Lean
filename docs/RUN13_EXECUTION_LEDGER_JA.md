# Run13実行台帳 — plan: docs/superpowers/plans/2026-11-10-run13-koszul-tor-foundations-order.md

基準：6b8d16889ea9b4d88567f0d9ac70391db2a49824（Run12）。branch work、着手時clean。
指令：origin/plan/run13-foundations-20261110 の aa133b92d5080dfb45a774e34313e721c35eeae5 をfetchし、指定文書を保存。
既存work checkoutと依存ビルドを継続使用。旧証明・旧検証原本を変更しない。通常Pushは継続許可済み。

## 完成条件

- [x] actual全原子e変数の最小表示、S₀とcut環の区別、完備比較の多項式線型性。
- [ ] 実変数の具体的Koszul微分・d²=0・augmentation・homology・自然性・上次数消滅。
- [ ] 通常TorとKoszul homologyの実比較、変数Koszulの有限自由解消としてのexactness。
- [ ] homology有限性・graded/total Betti、actual G/T/A/N/Qの必要な有限生成。
- [ ] 完全列・connecting map・rank Euler・必要な有界比較。
- [ ] 同標数体拡大の自然な複体/homology同型とBetti保存。
- [ ] 標準単項式/normal form・初項rank比較・±1 minor。
- [ ] Run12の完成環/同jump同型をactual Koszul/Torへ運搬。
- [ ] actual例・標数2・全回帰・全新宣言axiom依存・原稿台帳・独立レビュー・ZIP・commit/Pushとリモート照合。
- [ ] 実測による20run計画の再校正。未完があれば宣言・理由・依存を列挙。

## Pre-flight interfaces

Task1→2：各環の変数型と実作用を保つ。S₀→Gは全射ではなく、全原子環→Gを別に構成する。
Task2→3：実微分と通常のprojective resolutionを接続する。任意square-zero mapや比較を仮定するfieldを完成exportにしない。
Task3→4：chain group有限次元を仮定しない。有限P加群と変数null-homotopyからhomologyのk有限性を供給する。
Task2–4→5/6/8：自然写像を保持。異標数rank一致・全体T≅N・形式級数環全体のtensor同型は使用しない。

## ライブラリ調査

固定mathlibには通常のCategoryTheory.Tor、projective resolution、homological complex・homology完全列・ModuleCat基盤がある。
一方、Mathlib全ソースの名前/本文検索でKoszul複体の既存実装は見つからなかった。
これは通常Torの定義をKoszulへ差し替えてよいという意味ではなく、実変数解消・比較の追加証明が必要な境界である。

Ruling: ユーザーが指定した既存work checkout・通常Pushを継続 — 別worktreeへの移動で固定Lean/依存を複製せず、既存成果との接続を保つ — 誤れば監査対象branchの取り違えになるためHEAD/remoteと旧hashを照合する。

## 途中到達（Run13継続中・全体完成ではない）

- `Presentation.lean`：型を保持したgeneric VariableRing/augmentation/variableOperator、actual AtomExponent(e個)、全原子環→G全射、degree-one同値と線型関係なし、全原子作用でのcompletedPolynomialLinearEquiv。ビルド通過。
- `PolynomialModules.lean`：S₀→全原子環の作用整合、actual Tでのx変数削除(removeXPolynomial/terminal_removeX_action)、G/A/Qの有限多項式加群性、Noetherian係数環でT/Nの必要な有限生成。full PとS₀の完成環比較線型同値。ビルド通過。
- `KoszulComplex.lean`：実変数scalar coneの反復による具体的subset-recursion複体、d²=0、homology、chain groupの上次数IsZero。k有限次元を仮定しない。ビルド通過。
- `KoszulNaturality.lean`：scalarConeFunctor/koszulFunctor、任意P加群写像のchain map・homology map/iso、homologyの上次数IsZero。ビルド通過。
- `KoszulFinite.lean`：各chain groupの有限P加群性、ker/im商との同型、Noetherian性からhomologyの有限P加群性。k有限次元性はまだ全変数annihilationを要する。ビルド通過。
- `KoszulContraction.lean`：新しく追加した変数のscalarConeRaisingと明示的null-homotopy。ビルド通過。
- `StandardMonomials.lean`：全ideal要素の初項から定義した標準指数、実除法によるnormal form存在/一意性とactual商の標準単項式基底。未検証Gröbner候補を入力にしない。ビルド通過。
- `MinorRank.lean`：整数±1 minorの任意標数非零性、明示的有限列matrixのrank下限。ビルド通過。
- `ActualKoszulTransport.lean`：完成接錐の全原子/S₀線型同値と同jump層の実S₀線型同型をKoszul複体/homologyへ運ぶ。通常Torの比較とgraded homology shiftはまだ後続接続。
- `KoszulLowDegree.lean`：d=(-d_old, X+d_old)の実block公式とH₀のactual境界商への同値。ビルド通過。
- `KoszulAugmentation.lean`：H₀(M)≃M/(変数作用)Mのactual境界range同定。build21で通過。

## 到達点の確定（Run13全体は未完）

以下は全体build53までで証明した追加境界。最終の検証結果は `verification/block13/verification.json` を参照する。

- `KoszulAugmentation`：H₀の境界rangeと実変数作用部分加群の同定、実商との同値。
- `ConeExactness`：regularなscalar coneの正次数exactness。cycleの成分を実際に追跡し符号を検査。
- `KoszulPolynomialResolution`：実変数idealのprime性・未処理変数の非所属からregularityを供給。相異なる変数列の正次数exactness、各chain groupの自由性。
- `KoszulResolution`：全変数列とaugmentation、H₀でのexactness/全射、正次数exactnessにより本物の `ProjectiveResolution` を構成。
- `KoszulTor`：P線型加法的functorとの複体同型、解消をMとtensorした複体との同型、mathlibの通常 `CategoryTheory.Tor` とのobjectwise同型。第二因子kを解消する規約。
- `KoszulAnnihilation`：証明済み解消のprojectivityから全変数のnull-homotopyを構成しtensorで運ぶ。homologyの実P作用はaugmentationへfactorする。有限P生成性からk有限次元性を証明。
- `Betti` / `KoszulFree`：有限P生成のinterfaceでtotalBettiを定義し、通常Torへの係数線型同型、上次数消滅・加群同型による保存、自由PのBetti=(1,0,…)。
- `ActualTorTransport`：実Gと完成接錐の全e変数Tor/totalBetti保存、同jump層のS₀-Tor/totalBetti保存。T≅N全体の加群同型は使用しない。
- `FieldExtension` / `KoszulCoefficientBaseChange`：実L⊗ₖ複体のflat homology比較、有限性と次元保存、L⊗ₖk[X]≃L[X]。**変更後のL[X]加群のKoszul複体との同定は未完**。
- `HomologyRanks`：実短完全複体のconnecting mapに対して、隣接する補正rankの次元式を正次数とH₀で証明。**Koszul functorが加群短完全列を短完全複体へ運ぶ接続は未完**。
- `PresentationGrading`：全原子表示写像が任意次数の斉次多項式を実tangentDegreeへ送る。
- `StandardMonomials`：基底ベクトルが実商の標準単項式の類であることも明示。

## 正確な未完境界

`docs/RUN13_REMAINING_DECLARATIONS_JA.md` に必要な宣言と前提の供給元、受入検査の不足を記録する。
`X_BASIC` / `I_FIELD` 全体を閉鎖済みとは数えない。Run14のactual cutへ進む前にRun13の継続が必要。
途中で失敗したLean試行を定理の仮定へ移していない。新しい公理・sorry・未証明のcomparison inputは導入しない。

## 証明済み部分の検証

`verify_block13.py`：55コマンド、970 axiom report、旧84 hash一致。
新規core23ファイル/1,852行/183宣言/88 theorem、fixture46宣言を全監査。
許容公理のみ、警告なし。独立レビューのP3文言2件を反映。
検証statusは `PASS_PROVED_EXPORTS_RUN13_INCOMPLETE`。全体未完のcheckboxは変更しない。

## 継続（基準92cbe8f、ユーザー「最後まで終わらせて？」）

既存work・Push許可を継続。完成条件を保持し、Run13未完を閉じるまで実装を続ける。
Ruling: 基準92cbe8fの証明済みexportは再実装せず、component-mapの自然性を共通基盤として不足接続を追加する — coneの実分解を共有すれば短完全列・graded・base-changeに同じ写像を使える — 誤ればTor比較の可換式が別写像になり得るため各成分で照合する。
最初のRED：tests/KoszulExactness.lean。未供給のkoszulFunctor零写像保存とkoszul_shortExactを確認。
Ruling: koszulFunctorを「obj=実koszulList、map=実再帰koszulMap」のfield表示へ整理 — 以前はfunctor全体のxs-recursionのためobj一致が命題的で、同じ実写像の可換式に型transportが混入した。変数作用・微分・mapの再帰内容は保持 — 誤れば旧自然性/transportが変わるため全旧exportを再ビルド・回帰する。
継続到達：build22でTor比較自然性（koszulMapFunctorIso_naturality / tensorKoszulIso_naturality / torKoszulIso_naturality）が通過。
build19でL⊗ₖMの実L[X]作用と係数線型同型・pure tensor変数作用が通過。
build12で実filtrationのcokernel商homologyによるboundedFilteredComparisonが通過。
これらはRun13全体の完了判定ではない。次はchanged-polynomial functor/複体同型・Betti保存、graded接続・極小解消rankを継続。
継続到達：build28でkoszulPolynomialBaseChangeIso、実L[X]有限生成、koszulPolynomialHomologyBaseChangeIso、totalBetti_baseChangeが通過（L⊗ₖMの実作用を先に構成）。
build31でordinaryTorKoszulNatIso、ordinaryTorFunctorの加法性、実torConnectingとmiddle exactness/両合成0が通過。
build25でpartialEuler_sum / partialEuler_syzygy / rank0非負・末端消滅が実exact有限ベクトル複体について通過。
build35でDirectSumHomologyの一般exact direct-sum比較が通過（ModuleCat AB4、無限chain groupも可）。

### 残りの実装方針（継続用）

- 通常Torの全体balancingを新規公理にせず、実minimal free towerのsyzygy短完全列と証明済みKoszul LESでrank橋を証明する。入力は実自由加群・実exact covers・inc.image⊂実変数部分加群という通常の極小性。極小解消の存在は使わない。
- H0-map zero補題：chain f0.image⊂range d10ならopcyclesMap=0（pOpcycles epi・商のzero iff boundary）、H0=opcyclesからhomologyMap0=0。Koszul zeroIsoの自然性で実minimal incから供給する。
- 自由P加群の正homology消滅は、free⇒flatとtensorKoszulIso、exact functorのhomology比較から供給する。
- graded構成は次の具体案：入力GradedPolynomialModule(M)にpiece(q):ModuleCat k、実incl(q):piece→coefficientM、DirectSum.toModule inclのbijective、実Xiに対応するvar(x,q):piece(q)→piece(q+1)と可換式を持たせる。これは通常gradingのwitnessでありTor比較の仮定ではない。actual G/T/A/N/Q・strataでwitnessを供給する。
- graded chain pieceは「係数次数q」で再帰する：nil i0=piece(q)、nil i>0=0、cons i0=old0(q)、cons i+1=old_i(q)×old_i+1(q)。実chain inclusionもinl/inrで再帰。内部次数tの複体ではq=t−iとする（dはq→q+1）。
- 実変数のpiece operatorも同じproduct対角再帰。graded dは実coneの(-d_old, X+d_old) block式で再帰し、actual chain inclusionとの可換式を証明する。d²は実d²とincl単射から導く（別square-zero入力を置かない）。
- DirectSumのproduct同値はlmap(fst/snd)とlmap(inl)+lmap(inr)で証明可能。これとcofiberの実product同値からchain inclusionのDirectSum.toModule bijectiveを帰納し、DirectSumHomologyIsoで実Hのgraded直和分解へ進む。
- actual grading witnessは基底のdegree partitionから作る。Σq,{i//degree i=q}≃I、Finsupp.domLCongrとsigmaFinsuppLequivDFinsuppで実sum decomposition。pieceはdegree fibre finsupp、inclはbasis.repr.symm∘extendDomain。varは実Xiの基底座標をdegree(q+1)へsubtypeDomainする；homogeneityからextend戻し一致を証明。
- actual Gの基底指数carrier、TはTerminalExponent、AはHeadExponent、NはNonAperyExponent、QはAperyExponent。Run12のbasis/coordinate/degree、PolynomialGrading/PresentationGradingの実Xi degree+1を使う。元k作用とcoefficient restrictionはalgebraMap_smulによるidentity linear isoでつなぐ。
- same-jumpのdegree shift sはRun12の同じ実mapをpiece(q)→piece(q+s)へ制限し、再帰block map・graded complex iso・homology finrankへ運ぶ。
継続到達：build90–92でfullGGrading / nonXGGrading / actualAGrading / actualQGrading / actualTGrading / actualNGradingを既存のactual degreeとcoordinate supportから供給。一般grading witnessだけに留めない。
継続到達：build95でprincipal_totalBetti（非零のaugmentation ideal内の実principal関係のβ0=β1=1）、実minimal syzygy coverからのtoProjectiveResolution/minimalResolutionBetti、全Tor LES両端exactnessが通過。
継続到達：build82でgradedBetti_total（実signed complexの内部次数分解、finite total Hからfinite degree supportと有限和）通過。chainのk有限性を仮定しない。

### Final review → one fix pass（継続中）

独立レビューは `docs/RUN13_CONTINUATION_REVIEW_JA.md`。Criticalなし、Important2件。
Ruling: inherited extension gradingだけではactual L側の独立したorder-gradingとの同定を完成扱いにしない — レビューImportant1はTask6の要求に該当する — 無視すればactual graded Bettiの不変性を未証明のまま閉鎖してしまう。
Ruling: exactness acceptanceのModuleCat universeは意図した0を明示する — libraryはk σと加群universeを同じuで定義しており、テストの独立universe推論が原因 — 誤れば高universe対応を検査したと過大報告する。高universe renameはこのactual P14 scope外。
Final: Ruling: minimal resolution存在/全対象Tor-balancingは追加しない — given actual minimal coverから本物のresolutionとrank橋が証明済みで、存在を使う定理がない — 後続が存在を使う場合は別途供給が必要。
Final: Ruling: cut・局所化rank0・actual tower/connecting rank・harmonic initial ideal・公刊入力/最終P14は後続入力として保持 — 指令の責務境界に一致 — 後続でこれらを一般補題の仮定のまま最終P14に使うことは不可。
Final: Ruling: archive/progress/commit/pushは形式検証とfix完了後に実行 — 完成を先取りしない — 最後の公開まで未完ならrun完成とは報告しない。

Current verified state: core build134=4938jobs green（CompletedGradedTransportをt+0の巨大finrank rewriteからiso末尾のeqToIsoへ修正し9.5秒で通過）。
Full suite verification4は旧Block01–12全回帰を通過、new acceptance KoszulExactnessでuniverse mismatch RED。その後のenvironment auditはまだ実行していない。
途中版verification/block13とPARTIAL ZIPは凍結。新しいverify_run13_continuation.pyは環境から全生成宣言/structure projection/constructor/recursorを列挙する。

Important2 RED→GREEN: tests/KoszulExactnessのModuleCat.{0}明示で単体検査通過（exactness_universe_green.log）。
Important1 RED: tests/ActualGradedBaseChange.leanで、独立actual L gradingを両辺に持つ5つの未供給定理を検査。actual_graded_base_change_red.logに全5件のmissing exportを保存。
Fix strategy: GradedScalarComparisonには既存actual polynomial eと、各actual degree pieceのL tensor同型・inclusion可換式を持たせる。actual coordinate fibresからこのデータを証明供給する（target gradingをtransportで置換しない）。
KoszulScalarComponentsは既存polynomialKoszulTotalIso e xsの実inl/inr成分式を証明する。scalarKoszulGradePieceIsoは同じ外積blockの再帰（nil/0、zero、cons0、cons正次数product）で構成。
各chain grading inclusionとの可換式をinl/inr成分式で帰納し、rangeEquivをbaseChangeして実gradedKoszulSpaceの同型へ変換。既存total chain isoのcomm式とtarget inclusion単射からgraded複体可換式/diffを得る。
最後にcoordinateDegreeInclusion_coordinate（degree fibreの座標値）とcoordinateBaseChangePolynomialIsoのpure tensor座標式から5actual対象のGradedScalarComparisonを供給し、actual L gradedBettiを閉じる。

Important1 fix到達：build143で全4958jobs green。
`GradedScalarComparison`の実degree piece同型をKoszulの同じ外積block再帰へ運び、`gradedScalarKoszulIso_commutes`で同じtotal比較・actual inclusionsとの可換性を証明。
`ActualGradedBaseChange`は全5対象の独立した既存L側order-gradingを使用し、actualG/T/A/N/Q_gradedKoszulBaseChangeIsoとactualG/T/A/N/Q_gradedBetti_baseChangeを供給。
actual_graded_base_change_green.logとclosure_fixtures_green.logの単体検査が通過。source条件を弱めず、transported target gradingへの置換もしない。
型推論の負荷を避けるためBettiへの帰結はgeneric gradedScalarBetti_baseChangeへ集約し、実対象ごとの巨大なfinrank式展開を避けた。
全suiteはverification5を実行中。environment audit以降・最終文書・ZIP・Pushはまだ未完。

環境audit初回（verification5）で1284宣言（core1207/test77）の全依存は許容3公理内だったが、検証scriptの「ConstantInfo種別axiomは常に追加公理」というassertが失敗。
固定Lean4のLean/Util/CollectAxioms.leanを読み、module export時に検査済みproof bodyがaxiomInfo stubとなる一方、依存はprivate kernelで計算してexportedAxiomsExtへ保存されることを確認した。
Ruling: imported ConstantInfoの種別だけで数学公理と判定せず、Lean自身のcollectAxiomsと自己依存を検査する — コンパイラのproof-erasure stubと真正公理を区別する必要がある — 誤れば公理の混入を見逃すため、許容3公理以外・新宣言の自己依存・ソースの明示axiom/sorry等をすべて拒否し、exported_kindも原形保存する。
これは検証器の誤判定の修正であり、数学ソース・証明条件・公理の許容範囲は変更しない。修正版の全suiteをverification6で再実行する。


## 継続の最終到達・形式検証

- 指定Run13のTask1–7の必要exportとactual接続を閉じた。数学的な未完宣言はない（後続run入力は別表に保持）。
- Task8の全形式検証：verify_run13_continuation.py、40/40コマンド、全受入・旧Block01–12回帰・過去監査境界・schedule成功。
- core69ファイル/5,895行、named宣言458/theorem217。Lean環境からcore1,207/test77、旧741レポートと合わせ2,025件の依存を確認。
- 許容公理propext/Classical.choice/Quot.soundのみ。ソースaxiom/sorry等なし。新宣言自己依存なし。旧84 hashと固定環境一致。
- 独立レビューImportant1/2を1 fix passで修正し、それぞれRED→GREEN、全suite40/40。Critical/Deferred minorsなし。再レビューは追加しない。
- 原稿台帳A34–A40、20run再校正、宣言/仮定一覧、actual L gradingの不足と補強経路を保存。
- 途中版検証とPARTIAL ZIPは凍結（sha256 bd5e2d4195518c671ec3b7db87dc424f7eb0354e4351f8062bdbfdf10ee2c56b）。
- final COMPLETE ZIPはMANIFEST全payload hashとCRCを再読照合する。公開はこの台帳とZIPを含むworkコミットを通常Pushし、最終応答でremote SHA/cleanを照合する。

検証コマンド合計162.632秒（キャッシュ使用。研究/実装/初回依存ビルドの時間ではない）。
Rulingの全一覧はRUN13_RULINGS_JA.md、source snapshotはverification/block13_continuation/SOURCE_SHA256.json。
