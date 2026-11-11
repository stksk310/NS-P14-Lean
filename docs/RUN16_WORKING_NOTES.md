# Run16 working notes (same run, not a completion report)

Baseline447b7ae782414b739968a2a3009dd3a52ae230d0. Plan0cda4e8597ea1bafa8770b851ff2373973ee0e03 fetched and stored exactly in docs/superpowers/plans/2026-11-10-run16-endpoint-kernel-transfer-order.md.
No applicable AGENTS files. Work branch clean at start, origin/work same, no Run15 audit/fix branches found (only plan/run15). All Pushes remain user-authorized. Inline implementation; one fresh-context whole-branch reviewer at final per executing-plans skill, no implementer subagents.

## Current proved code

- Endpoint/Data.lean: broad EH Finset a, q=a.card, m,d,u, a positive and<u, u<m, d>=1, gcd(a.gcd,u)=1 and Nat.Coprime m d. No du<m or gcd(m,u)=1. Actual closure NumericalSemigroup cofinite from mathlib Nat.exists_mem_closure_of_ge; actual atoms exactly generators; multiplicity=m, e=q+2, width=d*u.
- Endpoint/OffsetOrder.lean: q+1<=u, strict sorted internalOffset:Fin q→Nat, actual membership/positivity/<u.
- Semigroup/WidthNormalization.lean: actual S.atoms offsets incl0, offsetGcd positive, coprime(m,d), normalized offset set, internal offsets, endpointData for e>=4,width<=m-2. Keeps m unchanged; generators exactly original S.atoms, carrier exactly S.carrier, q+2=e, d*u+2<=m.
- Endpoint/Presentation.lean: full variables subtype D.offsets (q+2), E=Fin2 variables, internal T indexed by D.a (q). Actual full polynomial AlgEquiv via rename to source.AtomExponent; E/T→full injective (not independence of images in G). fullG is actual G restricted through that equivalence; intrinsic Betti equality proved.
- Semigroup/CarrierTransport.lean: same actual carrier but different conductor witnesses gives same order, graded pieces, actual graded algebra equiv respecting pieces and initial monomials, completed cone equiv, intrinsic Betti equality. Proof by cases S,T,carrier equality; other cofinite/conductor data does not affect the definitions. Section Prop h must be included explicitly for theorem signatures!
- Endpoint/Normalization.lean transports normalized presentation to ORIGINAL S's G/completed G/full Betti.
- Endpoint/Core.lean: corePoints=AddSubmonoid.closure(range b↦(1,b)) in Nat². Genuine Core k=AddMonoidAlgebra k corePoints. coreValue→source.carrier, coreDegree/coreOffset add homs; B<=u*n and actual HasLength(nm+dB,n). coreInitial is actual DirectSum degree n monomialClass (may be0). Actual AlgHom coreToG via AddMonoidAlgebra.lift. Actual live/dead monomial criterion proved.
- Endpoint/CoreMap.lean: maximal actual atom representation gives core point degree=order and same actual initial monomial. coreToG_surjective. fullToCore:FullRing→Core and actual diagram coreToG.comp fullToCore=fullToG.
- Endpoint/CoreKernel.lean: liveValue_injective (actual value injection on live points), actual coordinate coefficient extraction, exact linear kernel=span of dead coreMonomials. No rank/kernel input.
- Endpoint/Coordinates.lean: epsilon, Coordinate=Fin u×Nat×Nat, decode=(L+K+epsilon,r+uK), coreCoordinates inverse to actual CoordinatePoint subtype. Exact nonnegative budget and unique coordinates. E-module/fiber ideal decomposition still pending.

All ten production modules above have independently built without warnings (928 total lines at this stage). Last root append CoreKernel/Coordinates building /tmp/run16_coordinate_root.log. Full regression NOT run yet; Run16 NOT complete.
Task1 tests EndpointData/EndpointNormalization/EndpointPresentation/CarrierTransport passed, incl du>=m sample and noncoprime endpoints. EndpointCore passed before exact-kernel test added; must rerun after latest root build. EndpointCoordinates RED recorded, must now GREEN. Red logs verification/run16/red/*.log. Current imports root append-only to baseline.

## Immediate next actions

1. Finish root build and tests EndpointCore / EndpointCoordinates, record ledger/provisional status and internal checkpoint (no final response).
2. Define coordinate fiber coreFiber r={ (L,K) | decode(r,L,K)∈corePoints}, E-upward closure and actual E-module ideals/direct-sum equivalence. Need finite internal-word generating list and Min antichains, nonzero every residue, Hx<=u-2.
3. All-long-competitor classification: p dead iff exists j>=1, q=(n+jd,B-jm)∈corePoints, with j*m<=B. Use maximal actual atom representation and gcd(m,d). Consider refactoring CoreMap to expose exists_corePoint (degree=order,value=x), since these equalities are currently internal to exists_coreInitial; can avoid inefficient recovering from equal images.
4. Prove finite stopping, carry/height/antichain bounds, exact actual fiber kernel N=M∩T, then homology/transfer/Artin/rows, all11 IDs. Do not stop at helpers/checkpoints. Keep old Run15 source/evidence/ZIP frozen.

## Mathematical routes worth reusing (not yet proved)

- Fiber minimality/finite list: choose minimal coordinate below any point via well-founded sum. A minimal core fiber point has a pure internal-word representative. If word length>=u, two prefix residues coincide (Fin(len+1)→Fin u pigeonhole); contiguous segment has offset c*u, 1<=c<=length-1. Replace segment by x^(length-c)v^c, reducing both coordinates for remaining word and contradicting minimality. Thus Min points have internal word length<=u-1; r!=0 gives L+K<=u-2, r0 min(0,0). Gives finite bounded list rather than only Noetherian existence.
- All residues nonzero: auxiliary monoid closure of a∪{u} has gcd1, hence cofinite by Nat.exists_mem_closure_of_ge. Obtain an internal word for every residue; u letters are removable modulo u. Choose shortest internal word. Repeated prefix residues delete nonempty segment preserving residue, contradicting shortestness; therefore length<=u-1. This avoids requiring an individual a coprime to u.
- E_HOMOLOGY easier alternate Euler: since v^m=0 and G finite E, H0(x;G),H1(x;G) are k finite (finite E, killed by x and v^m). Actual v cone on x complex is endpoints Koszul. Its real LES self-map ranks imply H1=H0+H2 directly. Avoid Hilbert syzygy/free-resolution existence/localization and never require k-finite G. Needs proof of finite k homology with variables nilpotent; candidate only until implemented.
- E_TRANSFER: existing correctedActionComparison already retains genuine H0 and requires only finite native homology. Apply to endpoint complex plus actual internal list; higher endpoint homology support1/2 gives desired binomial terms. Then compensate actual QC→QG kernel by real LES and finite-k chain bound. No spectral degeneration input.

## Lean gotchas observed in this run

- AddMonoidAlgebra is now a STRUCTURE with .coeff, not a Finsupp alias. Use AddMonoidAlgebra.single, coeffLinearEquiv k, supported_eq_span_single, .of_apply. Its induction_on has of/add/smul cases; .of carries Multiplicative.ofAdd; simplify ROOT lemma toAdd_ofAdd (not Multiplicative.toAdd_ofAdd).
- Avoid dependent degree rewrites in DirectSum monomialClass: apply DirectSum.of_eq_of_gradedMonoid_eq, then S.homogeneous_mk_eq k degreeEquality, then actual representative equality. Ordinary rw/simp may refuse to rewrite degrees and leave unsafe implicit-type expressions.
- coreValue(generatorPoint b) is not rfl because 1*m must simplify. CoreMap.coreGeneratorPoint_value proves it explicitly.
- Subtype sum coercions: change to source.carrier.subtype (sum ...) then rw[map_sum]. .subtype is genuine AddMonoidHom.
- Ring E independent of D requires explicit phantom binder (_D:Data), otherwise Lean drops section D and D.EndpointRing fails.
- Predicate section vars disappear from theorem signatures unless conclusion mentions them or include h in. Docstrings must follow include h in, not precede it.
- Some opaque defs in simp do not unfold id/function applications; change before omega/rw when necessary.
- Use PATH=/tmp/ns-p14-lean/bin:$PATH. One lake build at a time. Direct independent lean tests may parallelize. Root olean is removed during root rebuild: do not race tests importing NSP14 against an ongoing root build.
- Git mutations need exec_command sandbox_permissions=require_escalated (authorized, no need to ask user). Prefix git. Explicit fetch refs/heads/work:refs/remotes/origin/work before final Push, normal no force, remote SHA+clean verify.
