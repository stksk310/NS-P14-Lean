# Run15 whole-branch review package

Base:20aadbf7011692eb3bfffef49029e2c5e416ef3d (source basefbfa5de + parallel Run14 reproduction repair).
Review head: first Run15 partial-export commit, recorded in git log after verification.
This is an explicitly PARTIAL mathematical implementation, not a Run15 completion request.

Read-only review. Do not edit checkout/index/HEAD or dispatch agents. Review every new source and acceptance file, plus verifier and documentation. Check whether implemented theorem types actually express the claimed mathematical objects, implicit instances/assumptions, hidden unresolved theorem inputs, finite-chain misuse, boundary/index errors, and evidence claims. The known unproved goals must stay plainly unproved. Distinguish suitability for publishing partial progress from whole Run15 completion. Give concrete Critical/Important/Minor findings, file/line references, declined-to-judge list and verdict. Return findings in your final response; the primary agent records them.

## Plan and spec

- docs/superpowers/plans/2026-11-10-run15-actual-tor-target-ordinary-order.md (entire file)
- docs/RUN15_REMAINING_DECLARATIONS_JA.md (precise closed/unclosed boundary)
- docs/RUN15_CLOSURE_STATUS.json
- docs/RUN15_EXECUTION_LEDGER_JA.md (Ruling lines)
- docs/LEAN_PAPER_ALIGNMENT_JA.md A50–A54
- verification/run15/verification.json and compressed declarations/types/axioms
- audit/run15/RemainingGoals.lean: definitions of propositions, no proofs; production does not import it.

## Review Focus (verbatim)

1. **環を三つ区別する。** 有限長層はP=L[λ₁,…,λᵣ]、sourceの相対環はR=L[x,λ₁,…,λᵣ]、intrinsic Bettiは全e変数環。`cutG`をP有限生成又はk有限次元と無条件に扱わない。
2. **topと次数0を保持する。** 有限長P加群のcᵣᴾ=0と、sourceのcᵣᴿ(G)を混同しない。Rはr+1変数なので必要な末端はcᵣ₊₁ᴿ(G)=0。j=1ではc₀=極小生成元数、全変数への移行ではH₀の定数補正を省かない。
3. **同じwitnessを使う。** Run14で選んだ拡大体L・cut・P・tower・Hだけを用いる。同jump同型の次数差sを保ち、globalなT≅Nを仮定しない。
4. **任意標数の実rank評価を行う。** ±1 minorは実行列で示す。有理重みj/(t+j)は整数rankの数値評価であり、係数体で分母を割らない。後続微分の消滅や任意商のBetti単調性を仮定しない。
5. **actual targetと真正な最小表示を保つ。** source・target・相対環の変数数を区別する。一般APの最小性・gcd、ideal/quotientの添字差、Dの剰余端点、範囲外0、有限体からの下降を検査する。


## Files to inspect

- NSP14/ArithmeticSequence/Apery.lean
- NSP14/ArithmeticSequence/ConeRegular.lean
- NSP14/ArithmeticSequence/Interval.lean
- NSP14/ArithmeticSequence/Order.lean
- NSP14/ArithmeticSequence/Source.lean
- NSP14/Homological/BettiEuler.lean
- NSP14/Homological/ExtendPrefix.lean
- NSP14/Homological/FiniteKoszulEuler.lean
- NSP14/Homological/LinearVariables.lean
- NSP14/Homological/PolynomialInjection.lean
- NSP14/Homological/RestrictedScalars.lean
- NSP14/Ordinary/CutFinite.lean
- NSP14/Ordinary/JumpEuler.lean
- NSP14/Ordinary/RelativeFinite.lean
- NSP14/Ordinary/RelativeInjection.lean
- NSP14/Ordinary/RelativePresentation.lean
- NSP14/Ordinary/TowerEuler.lean
- NSP14/Semigroup/AlgebraPresentation.lean
- NSP14/Semigroup/CutBasis.lean
- NSP14/Semigroup/CutPolynomialInjection.lean
- NSP14/Semigroup/CutRetraction.lean
- NSP14/Semigroup/IntervalCompletion.lean
- NSP14/Target/CoefficientComparison.lean
- audit/run15/RemainingGoals.lean
- tests/ArithmeticSequence.lean
- tests/ArithmeticSequenceApery.lean
- tests/ArithmeticSequenceOrder.lean
- tests/BettiEuler.lean
- tests/CoefficientComparison.lean
- tests/CutBasis.lean
- tests/CutFinite.lean
- tests/CutPolynomialInjection.lean
- tests/FiniteKoszulEuler.lean
- tests/IntervalCompletion.lean
- tests/JumpEuler.lean
- tests/LinearVariables.lean
- tests/OrdinaryTor.lean
- tests/RelativePresentation.lean
- tests/Run15Actual.lean
- tests/SemigroupAlgebraPresentation.lean

- NSP14.lean (append-only exports)
- scripts/verify_run15.py (fresh test cache, ordered imports, relocated checkout output path, frozen baselines, complete Lean environment/type audit)
- docs/RUN15_20RUN_RECALIBRATION_JA.md

The first full regression attempt hit one new test syntax error (literal0.choose); the correction is explicit (0 : Nat).choose. The final full verifier must pass before publication. A green result only certifies the implemented exports, never the remaining proposition definitions.
