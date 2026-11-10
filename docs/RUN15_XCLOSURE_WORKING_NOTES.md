# Run15 ongoing x closure (internal working notes)

Baseline 0604586a39f2b3579e995bbbc789df70cca07107 was verified (74 commands, all 4195 project declarations) and pushed to origin/work. The exact original HarmonicGoal and complete same-cut tower resource contribution are closed there. Do not overwrite verification/run15_continuation or earlier submitted evidence. The user explicitly corrected premature partial handoffs: continue this run; do not stop at helper files or this checkpoint.

New uncommitted green modules (not yet root imported / globally audited): ArrowCone, ConeDiagram, ZeroCone, ConeSuspension, AcyclicQuotient, ComplexEuler, TwoStepCone, CoefficientKoszulFunctor, CutXSequences, CutXComparison, KoszulListResolution, PolynomialRestrictionKoszul. FullListBetti is currently being compiled after adding missing BettiEuler import and include hall/hxs.

TwoStepCone now proves both the sharp reversed Euler inequality and an exact equality subtracting a real LES connecting rank. It requires finite endpoint homology only, never finite G/I chains. Its quotient-homology-zero lemma kills that actual correction above the endpoint Koszul range. This will close relative top c_(r+1), without assuming c_r=0 for relative G or universal Euler positivity.

CutXSequences constructs literal P-linear x, kernel/image/head sequences on actual C.cutG / C.cutT / C.cutA. CutXComparison.cutXKoszulCone_Euler_le proves the actual x-cone inequality c_j(cone x on K_P G) <= c_j^P(A)+c_(j-1)^P(T). It does NOT yet identify this cone with ordinary Tor over the r+1-variable R. Subsequent actual B evaluation still needed for the first full bound L_j + X2 + T.

Important elaboration fix: directly changing (S.map F).ShortExact into a ShortComplex.mk of F.map components caused 100-second WHNF expansion. Unfold the tiny source sequence definitions BEFORE mapping: `unfold cutXKernelSequence at h1; unfold cutXQuotientSequence at h2; dsimp only [ShortComplex.map] at h1 h2`. Then application is 1.4 seconds with default heartbeats. Temporary trace tactics have been removed. For nested coefficientFunctor homology finite proofs use the new generic coefficientKoszulFunctor_homologyFinite; keep finite instances explicit when useful.

Current next route (planned, not proved): identify ordinary relative Tor using the actual free resolution on `none :: (variableList k (Fin r)).map some`. KoszulListResolution constructs an actual resolution for any complete nonrepeating variable list; FullListBetti transports ordinary Tor to its coefficient homology. PolynomialRestrictionKoszul proves literal variable-renaming restriction compatibility and the identity coefficient complex comparison, but not yet naturality for x.

Possible efficient route avoiding full renaming naturality on infinite G: construct the kernel/image/head sequences first over the actual algebra G itself, then restrict them along W.relativeToG to R. Apply Koszul on only the some variables, then coefficient restriction and TwoStepCone. The cone of the none scalar is definitionally the full chosen-list complex. Only T/A endpoints need renamed-variable restriction comparison with same-cut P (via PolynomialRestrictionKoszul and a natural equality of scalar-restriction functors). Their P homologies are finite by existing C.cutT_finite / cutA_finite. Actual algebra-linear x sequences can use modules G, terminalIdeal, xIdeal, HeadAlgebra; restriction is exact. All R/P actions come from the same W.cut.

Alternative is to retain CutXComparison and prove naturality of polynomialRestrictionKoszulIso with respect to an R-module endomorphism x, then compare the two cones. Existing polynomial base-change naturality modules provide a template.

Still original Run15 gaps beyond this: actual B=A/X2 and its L_j evaluation; relative full-variable transfer preserving actual H0 action; general AP actual resolution/Betti and ring-cone equality; actual target Betti and ordinary closure. Do not add these as assumed constructor fields or certify a conditional inequality as closure. Final verification, whole-branch review, manuscript ledger, audit ZIP and normal Push remain required at true closure.

For future verification use baseline 0604586 and a NEW output directory such as verification/run15_xclosure, preserving all committed prior evidence. Root imports and manuscript/status documentation can be appended/updated honestly; older mathematical sources should stay frozen unless a real correction is needed.

## 追加：actual x接続と末端行が閉じた（作業継続中）

- `RelativeConeBetti.relativeSomeCone_Euler`：同じcutのactual x作用の写像錐を通常R Torへ接続済み。
- `RelativeXComparison.relative_Euler_le`：actual c_(j+1)^R(G) ≤ c_(j+1)^P(A)+c_j^P(T)。全j、GのP/k有限性なし。
- `RelativeTerminal.relative_Euler_terminal`：正確にr+1の末端が0。元のRelativeTerminalGoalを追加仮定なしで監査用定理として証明済み。
- `tests/RelativeXComparison.lean`：actual Gamma=<6,7,11>、標数2で第1x評価、r+1末端、P端点を直接適用しコンパイル済み。
- Lean上の注意：具体的なRatFunc係数体のもとで写像錐を再構築すると、選ばれるlimit/colimit内部データの定義的照合が高コストになる。`coefficientActionCone`を抽象係数体上で定義し、その同じ構成を使うことで閉じた。局所letでcomputed functorを別名化する場合も、書き換え前に展開しないと高コスト化する。
- `KoszulSlotComplete`で実slotの完全性を追加。`KoszulRankOneAction`は各変数作用が実constant射影を通る場合のboundary rank上界、`KoszulIndependentImages`は変数像の独立性から同じrankの下界を実±1 minorで与える。`SquareZeroEuler`が正確な有限first-order加群Euler公式を閉じる。
- 次の接続：actual B=A/highIdeal(2)を同じcutのfirst-orderモデルへ同定し、A/X2完全列と既存TowerRowを通す。モデル公式だけでActualTorToRowGoalを閉じたと扱わない。
- 一般APの実Betti、H0作用を保つ全変数比較、任意体ordinary全閉鎖は未完。数学的障害の証拠はないのでrunを続ける。
