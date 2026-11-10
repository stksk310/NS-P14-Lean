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
