# Run13 Important1 implementation continuation

Do NOT stop / publish incomplete. User explicitly requested finish all Run13. One final reviewer already finished; no more agents/re-review. Important2 test universe was fixed GREEN; Important1 is being implemented inline.

Current new files:
- `KoszulScalarComponents.lean`: total PL chain iso using EXACT `e` (actual coefficient-change map), normalization of inl/inr, `polynomialKoszulTotalIso_inl/inr`. Build136 ongoing when this note was written; high elapsed/CPU on this file at 800k heartbeat. Do not edit the file while its compile is active. Need inspect build136 errors later. Avoid blind polling.
- `GradedScalarComparison.lean`: structure C (pieceIso q: L tensor source actual piece -> target actual piece; inclusion_commutes for pure tensor1); `scalarKoszulPieceIso` from total PL chain comparison; `scalarKoszulGradePieceIso` recursively nil0 C.pieceIso, nilpositive unique zero, cons0 old, conspositive TensorProduct.prodRight then old-isos.prodCongr. Added to root. Not built yet if preceding component file fails.
- `CoordinateGradePieces.lean`: not yet root-imported. Coordinate degree inclusion coefficient formula, pure tensor coordinate expression of EXACT coordinateBaseChangePolynomialIso, fibre field-extension iso. Standalone lake env lean may be queued behind build136 lake lock; log /tmp/run13c-coordinatepieces1.log.
- `ComplexRestriction.lean`: not yet root-imported. Generic complexIsoOfRestrictions from full complex iso E, component degree isos f_i, actual monic inclusions and compatibility. This avoids re-proving d-commutation by block arithmetic.

Remaining concrete construction:
1. Prove `koszulChainGrading_inclusion_cons_zero` and `_succ`:
   new incl0(a)=source inrX0(oldincl0 a);
   new incl(i+1)(a,b)=inlX(oldincl_i a)+inrX(oldincl_i+1 b).
   These unfold grading.transport/prod and scalarConePieceEquiv.symm; likely rfl after change. ScalarConeZeroIso.inv at0 equals inrX using noRelation proof.
2. Define field coefficient total chain iso for arbitrary xs:
   `scalarKoszulTotalIso e xs := (coefficientChainBaseChangeIso k L σ (koszulList k σ xs M)).symm ≪≫ restrictL.mapComplex.mapIso (polynomialKoszulTotalIso k L σ e xs)`.
   Its component equals scalarKoszulPieceIso (identity coefficient alias maps), so primitive pure tensor component formula can use `.hom.f i` directly.
3. Prove `scalarKoszulGradePieceIso_inclusion` by xs/i induction. nil0 C.inclusion_commutes, nilpos source piece=PUnit so a=0, all maps preserve0. cons0 use inr formula and polynomialKoszulTotalIso_inr on pure tensor oldincl; source Fpoly.map inr acts as1⊗inr(oldincl). conspositive expand actual incl into inl+inr, TensorProduct.prodRight_tmul, IH on both, map_add and TensorProduct.tmul_add, plus total inl/inr formulas. This is the only substantive recursion still needed.
4. For q=t-i, build degree-space field iso:
   baseChange of `(sourceChainGrading.rangeEquiv q).symm`
   ≪≫ scalarKoszulGradePieceIso C xs i q
   ≪≫ targetChainGrading.rangeEquiv q.
   Actual gradedKoszulSpace is range inclusion by definition. Call it scalarKoszulGradeSpaceIso.
5. Prove its inclusion compatibility into total γ_i on pure tensors, from step3 and rangeEquiv apply_symm_apply, then arbitrary tensor by induction. `l⊗a=l•(1⊗a)` + L-linearity extends 1-tensor formula. Bundle it as composition equality of ModuleCat maps.
6. Build `actualGradedKoszulBaseChangeIso C xs t` using ComplexRestriction.complexIsoOfRestrictions:
   E=scalarKoszulTotalIso e xs;
   a=fieldExtension.mapComplex.map (gradedKoszulInclusion source t);
   b=gradedKoszulInclusion target t;
   f_i=step4 .toModuleIso;
   target inclusion component Mono via subtype injectivity (explicit ModuleCat.mono_iff_injective).
   Thus the graded d equation follows from the SAME actual total E and inclusions, no arbitrary square-zero input.
7. Supply C from actual coordinate gradings (all G/T/A/N/Q have same index I and degree function d across fields):
   pieceIso=fibre Finsupp basis baseChange repr (`coordinateGradeBaseChangeIso`).
   inclusion_commutes: apply target coordinate equiv.injective; ext i; use coordinateDegreeInclusion_coordinate over k and L; use coordinateBaseChangePolynomialIso_tmul for existing actual e; split deg i=q; source/target fibre coordinates map coefficients and 0/1. Existing actual e defined via coordinateBaseChangePolynomialIso, proof parameter hm irrelevant.
   Could write generic constructor for arbitrary coordinateGrading witnesses with same `deg`; prove then specialize each actual `actualCoordinateGrading` (fields .piece/.inclusion are definally coordinate fibres/inclusion; no need to change their variable proofs).
8. Actual field-specific graded complex iso and theorem names required by RED test:
   actualG_gradedBetti_baseChange, actualT/A/N/Q_gradedBetti_baseChange.
   Compare extendedGradedComplex vs separately existing fullGGrading L / actualT/A/N/QGrading L, NOT transported target.
   Derive finrank through complex homology iso + gradedBetti_baseChange already proved inherited.

After fixes: rerun full `PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_run13_continuation.py` (current script has dynamic Lean environment inventory including generated structures etc). Preserve old `verification/block13`+PARTIALZIP. Current closure JSON deliberately pending. Update all docs/LEAN_PROGRESS/ledger/audit with exact counts and new bridge; final archive script `scripts/package_run13_audit.py` only permits closure true. Then normal own commit/push work, verify remote SHA/clean. `.git` requires require_escalated under sandbox; standing authorization exists.

New progress after initial strategy:
- build137: KoszulScalarComponents GREEN (58s) after explicit scalarCone_map f arguments.
- build138: CoordinateGradePieces, KoszulGradedInclusions, GradedScalarComparison GREEN.
  ScalarKoszulInclusions only nilpositive Subsingleton/zero simplification errors; fixed for build139.
  ComplexRestriction only final redundant simp nogoal; removed in139.
- CoordinateScalarComparison generic constructor uses explicit fibre equivalences fk/fL (actual identity), actual inclusion equations hk/hL (actual rfl), and exact e pure-coordinate formula he. This avoids guessing homogeneity proof terms in coordinateGrading constructors.
- GradedScalarKoszul.lean now contains rangeEquiv-based degree-space tensor iso, inclusion compatibility and construction via complexIsoOfRestrictions. Added to root for build140.
- ActualGradedBaseChange.lean generated all five actual comparisons, complex isos and required graded Betti theorems; not yet root-imported/tested. Need add to root once dependency140 errors fixed.


## Fix pass implemented

Build143 succeeded (4958 jobs). GradedScalarKoszul contains both the degree complex iso and
`gradedScalarKoszulIso_commutes`, using exactly the total comparison associated to the given actual e.
ActualGradedBaseChange supplies all five independently graded actual L specializations and their Betti
invariance. The missing-declaration RED fixture is GREEN in characteristic 2 → RatFunc.
This strategy is now a historical implementation record; final verification/archive/push remain in the main ledger.
