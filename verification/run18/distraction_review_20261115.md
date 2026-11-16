# Run18 distraction/Hilbert continuation — independent read-only review

Reviewed frozen source `abf2dad5369509b3893a54eda25cce446b435a79` against previous reviewed source `ed7f5cda20f054142bc9d5eb04574707bda9d8a0`. This continues the whole-branch R06–R08 assessment and covers all six new Lex production modules, six named consumer fixtures, focused07/08/09 and selected axiom probes, public scope claims and retained-contract/evidence differences. No implementation, subagents, Lean/build/checker execution, repository/index/HEAD/cache mutation, or evidence rewriting. Only this report is written by the reviewer.

## Findings

Critical: 0. Important: 0. Minor: 0.

The mathematical constructions support the stated generic-field polynomial/quotient/graded-piece linear equivalences and whole Hilbert equality. Completed R09 evidence independently passes this review for that scope and the existing partial closures. This is not a Run18 completion assessment.

## Mathematical strengths and public semantics

- `NSP14/Lex/DistractionMonomial.lean:9` defines the actual finite product of selected linear forms. Its step identity and degree proof establish D(a+e_i)=L_i(a_i)D(a) and degree(a). No degreewise output basis is merely assumed.
- `NSP14/Lex/GenericDistraction.lean` uses independent polynomial coefficients indexed by (variable, step, coefficient). Both the selected q-by-q linear-form matrix and each finite monomial-degree matrix specialize to the identity by the same diagonal coefficient evaluation. Their determinants are therefore proved nonzero over every nontrivial commutative base ring; nonzero determinants are not asserted to be units there.
- `NSP14/Lex/GenericDistractionField.lean:12` takes the genuine fraction field of the coefficient polynomial ring over arbitrary Field k. Injectivity of its localization map preserves the proved nonzero determinants, which are then units in the fraction field. Actual linear equivalences are constructed from those matrices. This avoids the invalid inference that a nonzero determinant over the raw coefficient ring is automatically invertible. No characteristic-zero assumption, division by characteristic-dependent integers, or comparison of ranks in different characteristics appears.
- `NSP14/Lex/DistractionLinearEquiv.lean:31` connects the coefficient matrices to actual homogeneous polynomial spaces and their monomial bases. `:57` assembles these via the actual homogeneous direct-sum decomposition into a polynomial vector-space equivalence; `:63` proves the literal prescribed image on every monomial, and `:87` proves homogeneity in both directions. This is a field-linear equivalence, with no false multiplicativity claim.
- `NSP14/Lex/DistractionIdeal.lean:30` uses the inverse of the selected actual linear-form matrix to express each coordinate variable as a linear combination of the L_i(a_i). With the monomial step identity, `:57` proves closure of the distraction span under variable multiplication; `:88` extends closure to arbitrary polynomials. Thus `:101` is an actual ideal, not a vector space relabeled as one.
- `DistractionIdeal.lean:108` uses the monomial-ideal condition exactly where needed to prove image membership iff inverse-linear-image membership. `:140` identifies the actual ideal span; `:160` proves homogeneity. `:184` constructs a quotient field-linear equivalence from actual mapped submodules, with the literal quotient representative formula at `:193`. Neither a polynomial-module isomorphism nor ring isomorphism is claimed.
- `NSP14/Lex/DistractionHilbert.lean:13` is a field-linear degree-preservation lemma derived from actual homogeneous standard-monomial bases. `:63` and `:77` apply it to the quotient equivalence and its inverse; `:95` proves equality of the mapped actual degree spaces. `:108` gives actual graded-piece linear equivalences for every Int degree, and `:118` derives equality of the actual whole quotientHilbert function. This is more than an ungraded dimension count.
- The direct-sum and degreewise arguments do not require the complete quotient to be finite-dimensional over the field. Negative internal degrees are treated as Int-indexed grading pieces, with no saturated subtraction. q=0 and zero/unit monomial ideals are not excluded; the empty product/matrix and generic linear/submodule constructions retain their standard meanings.
- Every input ideal in the public distraction/Hilbert conclusions is explicitly over `GenericDistractionField k q`. This is an important honest limitation: these exports do not already extend an arbitrary original k-ideal, identify its scalar-extended Tor, specialize back to k, or descend any Betti inequality. Infinite coefficient families live in an actual polynomial/fraction field; no simultaneous specialization over an arbitrary finite base field is assumed.

## Fixtures and evidence available

The six named fixtures are actual consumers of the product identity, raw nonzero determinants, fraction-field determinants, whole polynomial-equivalence monomial images, actual ideal-image membership, and whole actual Hilbert equality. They retain arbitrary-field statements. They are generic contract consumers, not independent concrete Betti computations; neither the fixtures nor the public claims represent them as such.

Focused07 has three individually successful warning-free commands; focused08 has five; focused09 has three. Selected axiom probes report only propext, Classical.choice and Quot.sound and print the intended public equivalence/ideal/Hilbert types. root_build10 reports 6,178 successful jobs. Earlier elaboration failures remain in new logs; the ledger distinguishes the invalid gradedAlgebra-missing RED attempt from the subsequent missing-declaration-only RED control.

The public ledger and paper-correspondence entries explicitly state field-linear equivalence rather than ring/chain equivalence, that the ideal lies over the generic coefficient field, and that original-field scalar extension/descent, Betti preservation and lex termination remain open. The previous R08 validation is not represented as validation of these six later modules.

## Frozen scope and evidence hashes

RequestedGoals remains SHA256 `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`. Git delta shows no frozen-plan/RequestedGoals change and no modified/deleted previous verification/artifact files.

Recomputed SHA256 values agree with the final R09 source manifest:

- DistractionHilbert.lean: `f3637a1dfd3ae4d69acc1a4634a3408a1d85faef33e9e651218424a98eed4515`.
- DistractionIdeal.lean: `15531b5c31fe7ebef90455bd3f6aeaca2fde69b7ee4795ad02854b5f6a6ffd95`.
- DistractionLinearEquiv.lean: `462a257b988bff98159dbeb7124fafb0c722c5ceb6679a1219b268f425d726c1`.
- focused07.json: `5c734ed397cf7f8128516b43fc547976284b5ed9984ac5bb73c7959fcff0b06b`.
- focused08.json: `92290dfac75cabfdc6238ccd5be1f130f694557e83a36f5d12bfb1d37c2693bd`.
- focused09.json: `e41f94bd9f0075e352f208e46278d8624ffd97387c61b2d53b8a60bcebecbca5`.
- Axioms08_focused09.log: `9d22a04633964cd338935870fd8cc31f4194f25f14fa06b879ff193b88b8dccb`.
- root_build10.log: `1d7eb59e32be7e8313c1766dd8a2801f2f4f61046816653bba10a4eb6cc65397`.

R09 is bound to source `abf2dad5369509b3893a54eda25cce446b435a79`, Lean 4.36.0-rc2, mathlib `139105d28c7685a154cb3093f79edb2e16708099`. Its completed exhaustive declarations, manifests, regression outcomes and retained-byte checks were independently inspected as described below.

## Remaining obligations and scope

Hilbert preservation alone does not preserve Betti numbers. The new polynomial/quotient field-linear equivalences are not Koszul chain maps or module equivalences; actual Betti preservation/comparison for distraction remains unproved. Arbitrary original-field scalar extension/descent, the monomial-to-lex deformation/iteration and termination, and existence of one common-Hilbert lex ideal remain outstanding. Consequently full BHP/X_BHP_EK is still open despite the already-closed EK conjunct and prior actual initial-ideal comparison.

W_DENSE and W_CLOSE also remain open. The assigned closed IDs remain exactly W_SPARSE, W_FIVE and W_EDGE, retaining the original physical-width source/target scope. Received PDFs are available references, not formal proofs. The user's request to finish all Run18 is not satisfied by this internal checkpoint; no Run19 recommendation or Run18-complete claim is made.

## Completed R09 evidence assessment

R09 reports `PASS_RUN18_PARTIAL_VALIDATION`, explicitly `run18_complete: false`, with 224 recorded commands, 210 fixtures, 9,753 environment declarations and 1,512 new declarations. Every recorded check passed its intended condition; there is no failure.json. All six new consumer fixtures individually exited 0. The three expected-open controls exited 1 solely on the named absent declarations `NSP14.Lex.bhp_ek`, `NSP14.Run18.dense_closed` and `NSP14.Run18.width_closed`, rather than incidental import or elaboration failures. The publication guards and actual Lean axiom-policy controls passed. The negative axiom control rejects a genuine extra axiom; the positive proven-stub control is accepted and is not a production dependency.

I independently recomputed all 1,630 source SHA256 entries and all 240 evidence SHA256 entries. Every byte digest matches; the final evidence manifest covers exactly the run-directory files other than the manifest itself. Every source-manifest file also matches its Git blob at the frozen proof snapshot, and HEAD remains `abf2dad5369509b3893a54eda25cce446b435a79`. This binds the completed evidence to the actual source reviewed, not merely to a matching branch label.

All 5,037 retained verification/artifact files match their committed Git blobs. All 4,768 such files present at the previous reviewed source ed7f5cd are unchanged in both HEAD and working bytes. All 3,857 original baseline files remain byte-identical except the three permitted append-only files (NSP14.lean, LEAN_PROGRESS.md and docs/LEAN_PAPER_ALIGNMENT_JA.md), whose original byte prefixes are preserved. Frozen plan and RequestedGoals bytes match the prior reviewed commit; the original physical-width target V=d*u is not weakened. I also rehashed every entry in the retained R05, R06, R07 and R08 final evidence manifests (198, 204, 222 and 234 entries respectively), all matching.

I compared every raw environment record with the processed declaration record: names, defining modules, transitive axiom sets, ordinary types and explicit types agree; exported-kind metadata agrees with the raw output. All 9,753 declarations use only the permitted axioms `propext`, `Classical.choice`, `Quot.sound`, with no declaration appearing as its own axiom and no added project axiom admitted by policy. Lean's exported representation of some proved declarations as axiom-kind constants is not confused with a genuine extra axiom; dependency closure is the enforced distinction. Every declaration source hash matches current bytes. All 1,512 new declarations carry nonempty ordinary and fully explicit types, and every listed new source module has environment declaration coverage. The complete printed signatures and the public source definitions preserve the stated generic-field inputs and linear-equivalence conclusions; no hidden chain-equivalence, Betti-preservation or scalar-descent premise was substituted for a proof.

The cache record shows tests, Run18 audit artifacts and the complete Lex/Width production caches retired, along with the specified new Endpoint/Homological artifacts, before rebuilding. Thus the six new Lex modules and their consumers are covered by the fresh R09 execution. This is a fresh project/new-production verification with the recorded Lean/mathlib environment; it does not claim a fresh rebuild of all external mathlib dependencies. No reviewer build or proof execution was run, so these execution claims refer to the inspected, hash-bound R09 logs.

Final evidence digests:

- verification.json: `faa786267f58d9596eb650fd0f99f48dceb3e06e8324d555d5a6783da5a41067`.
- SOURCE_SHA256.json: `f503b203b16d0bdf2fd11291017802ccc359a8561b019316c87a80e769fec6a8`.
- MANIFEST_SHA256.json: `fedb3ac5790859f9ef4f13e6e88df66633ad3f454b993df33ea295acff2f86ce`.
- declarations.json.gz: `6b3993920472179d22ee63c5a1254e84c6047648cdd62d0c1af14dd1a366c09b`.

The completed R09 directory is currently untracked; it is the only status entry. Its content and source binding are verified, but no future evidence-commit binding is asserted.

## Final assessment

PASS for the reviewed generic-field distraction ideal, polynomial/quotient/graded-piece linear equivalences, and whole Hilbert equality, together with the unchanged previously reviewed partial closures. No pending review items. Declined-to-judge list: empty within the assigned scope. Later /tmp exterior/contraction experiments and all other uncommitted prototypes are excluded from this frozen-source review.

The separately proved EK conjunct and the three assigned closed IDs W_SPARSE, W_FIVE and W_EDGE remain supported. Full BHP, distraction Betti preservation/comparison and original-field descent, common-Hilbert lex existence/termination, W_DENSE and W_CLOSE remain substantive unproved obligations. Run18 is not complete.
