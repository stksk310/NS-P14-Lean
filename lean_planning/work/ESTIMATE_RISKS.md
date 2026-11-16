# Independent effort and risk estimate for a complete P14 formalization

Planning only, 2026-11-09. No Lean development or installation was performed for this estimate. The basis is the 50-node registry in `proof_structure_v3/lemma_registry.json`, its dependency map, and §§6–7 of `P14_REFEREE_READINESS_V03.md`. The repository's V03 architecture and internal audit pass establish a useful proof route; they do not establish the cost or completion of a Lean proof.

## What completion must mean

The final declaration must quantify over every genuine numerical semigroup, every field, and every total Betti row, and compare the actual tangent cone with the actual interval completion. Each ring must use its own minimal polynomial presentation. The mathematical meaning of Betti numbers must be connected to Tor, or to a proved equivalent construction. Defining numbers from the desired formula and subsequently comparing those numbers would not meet this target.

The project must prove the source model: semigroup membership and atoms, maximal representation length, Apéry coordinates, the semigroup ring and its tangent cone/associated graded, and the relevant polynomial presentation. A convenient combinatorial or polynomial model is welcome, provided an explicit proved equivalence connects it to the stated object. If a completed semigroup ring is replaced by an easier algebraic model, the associated-graded identification is a theorem to prove.

Every reachable published input and every component hidden inside `X_BASIC` must have a kernel-checked proof, or be replaced by another kernel-checked proof of the needed special case. A theorem with seven external inputs as hypotheses is useful intermediate progress but is a conditional theorem. Instantiating those inputs with newly declared axioms does not make it unconditional.

Normal Lean foundations such as classical choice, propositional extensionality, and quotient soundness may be accepted. The final dependency audit must disclose the precise accepted foundation and show no `sorryAx`, new mathematical axioms, or unproved application hypotheses. If an execution tactic introduces an additional trust assumption, disclose it; a strict kernel-proof milestone should use a proof-producing alternative. No blanket ban on classical mathematics is needed.

## Why node counting would seriously underestimate this work

1. `X_BASIC` is one graph vertex but contains several substantial libraries: Koszul computes Tor; exactness and its dimension inequalities; bounded double-complex/filtration comparison; finite-dimensionality; Hilbert syzygy or an adequate vanishing replacement; fraction-field Euler arguments; and Gröbner division.
2. `X_GREEN`, `X_BHP_EK`, `X_AP_BETTI`, `X_AP_CONE`, `X_KNESER`, `X_SC`, and `X_LTV` are roots with no incoming edges in the paper registry. Their formal proofs have their own dependency graphs. They are not zero-cost because they are published.
3. Finite rational tables and polynomial signs are relatively accessible. They do not prove that the quantities being bounded arise from the actual semigroup, the same cut, the actual kernel, or the actual target.
4. A proof for a supplied list of integer generators is not yet a proof for all numerical semigroups. Atom/minimality/order/enumeration equivalences and the target's distinct minimal presentation matter.
5. Replacing Betti by finite Koszul homology can reduce the amount of general homological algebra. The equivalence with intrinsic Betti numbers and all necessary finite-dimensionality and field-extension results still have to be proved.
6. A specialized finite double-complex inequality may be cheaper than a general spectral-sequence library. The specialization must retain the exact zeroth-homology row, filtration/convergence hypotheses, and the fact that later pages can only reduce the relevant dimensions.
7. Arbitrary fields require proofs that work in each characteristic. Rational counting coefficients are not division in the coefficient field. Unit minors must remain nonzero in characteristic two. Same-characteristic base change is distinct from comparing ranks in different characteristics.
8. A–D are semantic bridges, not cosmetic changes of notation. The ordinary route cannot identify all of `T` and `N`; the narrow route cannot replace `M_s ∩ T_s` by `T_s`; neither route may assume quotient Betti monotonicity or spectral-sequence degeneration.
9. The width-four proof needs both vanishing and linear independence to establish the initial-ideal equality. Four residue counts without that bridge are not its universal Gröbner proof.
10. A graph/link/hash audit and a compiler success for declarations with unproved inputs are valuable checks with different completion boundaries from unconditional P14.

## Effort model

One person-day means roughly six focused hours by a mathematician experienced in Lean and the relevant algebra, with AI assistance and ordinary review included. The estimates are expert judgments before calibration, not measurements from this repository and not a promise about autonomous AI wall-clock time. Paper proof correctness and access to the cited full proofs are assumed. Major changes to the mathematics can exceed the risk band.

The bands assume a pinned Lean/mathlib baseline, no unusually strong exact external formalization discovered after this audit, and a strategy of proving the special cases actually needed rather than developing every general theory. A public-source theorem-name search alone cannot establish library absence. Every proposed reusable result needs its statement, hypotheses, import path, and a compiling application checked before assigning zero implementation cost.

The preferred design to test is to define the relevant Betti numbers using the actual polynomial variables' Koszul homology and prove agreement with standard Tor separately. It should use the concrete finite double-complex dimension estimates needed here, rather than begin by implementing all derived functors, all minimal resolutions, or a general spectral-sequence convergence library. The published inputs should likewise target the exact degree-two Green consequence, dense Betti upper bound, AP formulas/equality, and other application forms actually needed. A proved specialized substitute is sufficient; merely assuming the specialized statement is not. The table already assumes this economy, so it should not later be counted a second time as an automatic schedule reduction.

The concurrent library audit reports useful associated-graded/Rees quotient support and substantial abstract spectral machinery, while its pinned Tor module documents major unfinished comparison work and its search has not established the needed concrete algebraic Koszul implementation. This points to interface development and concrete bridges, not a claim that all foundations are absent. Exact declaration evidence belongs in the library inventory; a pilot application is still needed to measure practical reuse.

Positive declarations reported in that audit include `Nat.exists_mem_closure_of_ge`, `Nat.addSubmonoid_fg`, `exists_frobeniusNumber_iff`, `ShortComplex.moduleCatHomologyIso`, `Module.Basis.exteriorPower`, and quotient/rank-nullity finrank results, on the mathlib snapshot using Lean `v4.36.0-rc2`. These are relevant building blocks for semigroup finiteness and linear/homological algebra. They do not by themselves identify the coordinate tangent-cone model with the actual associated graded or prove the application-specific Koszul–Tor and Betti comparisons. The inventory should record their exact hypotheses and revisions.

The rows below separate shared infrastructure from applications to avoid charging for the same Koszul or Gröbner development twice. They are work-package estimates, not a claim that the 50 paper lemmas already determine the best Lean module boundaries. Numbers are person-days.

| Work package / principal registry coverage | Optimistic | Working | Risk |
|---|---:|---:|---:|
| Pinning, statement and trust contract, dependency/application audit | 5–10 | 10–20 | 20–40 |
| Actual numerical-semigroup, semigroup-ring/associated-graded, Apéry and minimal-presentation foundations | 40–80 | 80–160 | 160–320 |
| Shared Koszul–Tor/Betti bridge, exactness, finite dimensions, field extension and vanishing | 50–100 | 110–220 | 220–440 |
| Needed bounded double-complex/filtration dimension comparison | 20–45 | 45–100 | 100–200 |
| Shared standard-monomial, initial-ideal and terminating-division tools | 20–45 | 45–90 | 90–180 |
| Ordinary actual coordinates, cut/tower, harmonic bound, A–B: `O_COORD` through `O_TARGET` | 45–90 | 90–180 | 180–360 |
| Ordinary Sidon, universal scalar signs, low/small/large-rank closure | 20–40 | 40–80 | 80–160 |
| Endpoint core, all competitors, actual kernel/carry and C: `E_CORE`–`E_TRANSFER` | 45–90 | 90–180 | 180–360 |
| Artin bounds, dense/sparse/five-generator branches and N4 general/small-width branches | 50–100 | 100–220 | 220–440 |
| Width-four application D: all-m competitors, initial-ideal equality and residue formulas | 20–40 | 40–80 | 80–160 |
| All seven published roots, proofs or proved adequate specializations; shared infrastructure above excluded | 160–350 | 350–800 | 800–1,600 |
| Global assembly, all-field/all-row boundary audit, clean rebuild and independent review | 20–40 | 40–90 | 90–180 |
| **Indicative arithmetic total** | **495–1,030** | **1,040–2,220** | **2,220–4,440** |

Do not interpret the endpoints as statistical confidence intervals. The optimistic band requires effective specializations, unusually good library reuse, stable definitions, and no substantial paper-proof repair. The working band is an initial staffing envelope. The risk band represents several difficult foundational/proof-porting surprises, not a guaranteed upper bound. Reuse discovered during a declaration-level audit should reduce the affected rows explicitly.

These pre-pilot numbers are not a measured lower bound of 1,040 person-days. A better specialized construction, more reusable results, or an independently developed formal input can change them substantially. Conversely, discovery of a mathematical scope problem can invalidate even the risk envelope. Budget decisions should use the pilot revision, not treat the current numbers as a commitment.

The seven-root allocation deserves separate review. BHP in arbitrary characteristic (including the needed positive-characteristic input), together with the lex/EK interface, is plausibly a major part of that row. Green requires its actual generic-hyperplane statement and the finite-field transfer. Arithmetic-progression Betti formulas require a verified resolution or another proof with the actual minimality hypotheses. AP tangent-cone equality is a separate theorem. Kneser, Savchev–Chen, and the three-generator result may proceed on independent tracks after their basic objects are fixed. None should be estimated solely by the short application paragraph in V03.

## Calendar interpretation and critical path

For calendar planning, use approximately 20 working days per month and reserve 20% for interruptions, maintenance and coordination: about 16 delivered focused person-days per month per fully allocated expert. This converts the totals to roughly 2.5–5.5, 5.5–12, and 12–23+ single-expert calendar years respectively. These are rough effort equivalents, not delivery promises. The person-day table already includes ordinary proof review and local iteration; the calendar reserve handles unavailable capacity and should not also be added to the table as a second review charge. A second or third suitably experienced contributor can run independent published/combinatorial/application tracks, but cannot divide the calendar mechanically: object definitions, exact statements, proof review, and many semantic bridges are sequential dependencies. Coordination and interface rework can add effort beyond the initial allocations.

The likely critical path is:

`actual semigroup / tangent cone / minimal presentation`
→ `Koszul–Tor/Betti and relevant finite-dimensional comparisons`
→ `ordinary A–B or endpoint C actual-source bridge`
→ `branch closure`
→ `all-root instantiation and global P14`.

In parallel, every published-root proof must be brought to the same interfaces. A late BHP, AP, or LTV theorem can become the critical path even if all local V03 inequalities are complete. Kneser and Savchev–Chen can be independent research tracks; they cannot bypass the endpoint-to-actual-source bridge needed at the application.

The earliest genuinely short deliverables are selected scalar identities, rational anchors, injection/counting lemmas, and finite matrix rank arguments. Their likely unit cost ranges from a fraction of a day for a literal exact identity to several days or weeks for a reusable universal inequality with all index conventions. Their completion should be reported as named local Lean theorems, not as a percentage of unconditional P14.

There are two importantly different conditional deliverables. A scalar lemma conditional on a numerical resource profile can be a small local project. A conditional P14 theorem about the actual semigroup/tangent cone, with only the seven published inputs left as explicit theorem parameters, still requires the actual semantics, Koszul/Tor agreement, A–D, and global integration. In the current work-package accounting, removing only the published-proof row gives 335–680 optimistic, 690–1,420 working, and 1,420–2,840 risk person-days. Those figures are as provisional as the full estimate. Removing the actual semantic work as well creates a different, weaker milestone and must be labeled that way.

## Milestones with explicit acceptance boundaries

| Milestone | Acceptance evidence | What remains |
|---|---|---|
| M0: exact formal target and baseline | Pinned project; intended objects and all-field/all-row statement; usable-declaration audit; trust policy | No assertion of a P14 proof |
| M1: verified arithmetic/combinatorial islands | Universal lemmas with explicit integer ranges and kernel-checked proof terms; source equation mapping | No actual Betti/source conclusion unless already connected |
| M2: actual algebra and Betti semantics | Proved equivalence of the chosen model with the stated tangent cone; atom/minimal-presentation results; Koszul/Tor/Betti bridge over arbitrary fields | Main inequalities and root theorems may remain |
| M3: semantic local branch results | A–D and relevant branch theorems on actual objects; any still-unproved published inputs visibly quantified | Conditional branches are explicitly conditional |
| M4: closed mathematical roots | Each needed published input has a proof or a proved replacement at the exact scope; all shared foundations are closed | Integration and global coverage review |
| M5: unconditional P14 | Final theorem has only intended semigroup/field/index hypotheses; dependency audit; clean rebuild; full range and minimal-source/target review | Ordinary maintenance only |

M4 can complete in pieces alongside M2–M3. The order is a completion boundary, not a requirement to postpone local mathematics until every library result is ready. Generated structures, placeholder classes, `axiom` declarations, or successful checking of a conditional final signature cannot satisfy M2–M5 on their own.

## Calibrate with two or three pilots before expanding the project

These pilots are proposals for a later authorized implementation phase. This planning pass does not create a Lean scaffold or install a toolchain. Use a small disposable project or isolated branch, pin it, and record outcomes. A timebox is a measurement budget, not a promise that the pilot will finish.

1. **Universal arithmetic pilot, 3–5 person-days:** prove one genuinely universal fixed-cutoff scalar identity plus its sign implication with the actual out-of-range binomial conventions. Include one five-row rational anchor. Distinguish proof of a finite list from proof for all parameters. This calibrates the relatively accessible layer.
2. **Semantic small-source pilot, 5–10 person-days initially:** attempt the e=2 chain from the actual semigroup to its associated-graded polynomial quotient and the Betti sequence `(1,1)`. Record the first unclosed prerequisite if the timebox expires. This is deliberately more revealing than defining an abstract ring already assumed isomorphic to the desired quotient; it tests the actual-object/minimal-presentation cost.
3. **Homology interface pilot, 5–10 person-days initially:** formalize one short-exact-sequence dimension inequality and the specialized two-variable Koszul homology or bounded double-complex comparison needed for C, preserving the exact H0 row. Connect it to existing complexes, or explicitly record what prevents the connection. An abstract numerical inequality supplied with homology dimensions as assumptions is only a partial pilot.

For each pilot measure: focused human time, AI iteration/review time, usable existing declarations, new prerequisite statements, completed proof terms, remaining hypotheses, dependency-audit output, and clean rebuild time. Classify blockers as mathematical, library-interface, elaboration/performance, or missing theory. Re-estimate each work package from these observations; do not extrapolate the arithmetic pilot's throughput to semigroup semantics or published theorem proofs.

An appropriate decision after the pilot phase is whether to fund the whole research program, narrow the initial theorem scope with an explicit label, or first contribute a needed reusable library. It is not a reason to silently redefine P14 or leave external inputs axiomatized while declaring the project complete.

## Conditions requiring an estimate revision

- An exact reusable formal Green/BHP/AP/LTV theorem is found and its application compiles: reduce the corresponding proof allocation, retain interface and review work.
- A verified direct finite-complex route replaces a general spectral-sequence/Hilbert-syzygy development: reduce the shared foundation allocation only after proving its sufficiency for every use.
- The completed-semigroup-ring/associated-graded interface or the definition of a minimal presentation changes: re-estimate downstream semantic packages before continuing broad implementation.
- An external paper theorem has a field/characteristic/scope mismatch: suspend the affected unconditional completion claim and price a proved specialization or mathematical replacement.
- A pilot closes only local arithmetic while actual semantic bridges remain blocked: retain the research-program estimate; this is not evidence for a short full-P14 schedule.

This estimate makes no assertion that a mathematical result is absent from mathlib based on keywords or filenames. The accompanying declaration/source audit, followed by compiling pilot applications, must establish which proof obligations are already covered.
