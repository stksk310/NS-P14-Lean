# Independent V06 mathematical source review

Review baseline: `a7504eea25f02728d1be6cd0082e8484d639dbe2`.
Workspace: `/tmp/ns-p14-v06-alignment-20261116`.
Proof commit: `d446fc2f18f7a8603d1eedd446e93810dc44d01c`. All 38 reviewed SHA256 hashes below were independently compared against both this committed tree and current worktree bytes and matched. A later commit is covered only if those contents match.

## Result and scope

Static mathematical/source review: **0 critical, 0 major, 0 minor findings**.

Reviewed all eleven modified production modules, both new production modules, all four new mathematical boundary fixtures, the named-root reachability fixture, umbrella append, and the supporting sources listed below. Read the full supplied order, implementation plan, and finite change policy. No AGENTS.md was present at applicable searched paths. Review was independent of implementation-agent success claims.

This is not Lean elaboration or full evidence verification. I did not build, run Lean, modify shared cache, check out, or commit. The only write is this report outside the worktree. I did not validate verifier/package/negative-control implementation, source/evidence manifests, raw-log authenticity, allowed transitive axioms, or compiled normal/explicit export equality. Those require the separate infrastructure review and verifier. Source inspection found no added mathematical axioms or `sorry`, `admit`, `sorryAx`, or `native_decide` in the seventeen changed/new mathematical Lean files. The named-root fixture adds only imports and #checks. Its explicit FiniteSocleBounds import was reread after the parent corrected reachability of competitor_zero_column; this affects the fixture only, not the three production import-closure roots.

## Mathematical and route conclusions

| Route | Source review |
| --- | --- |
| Endpoint | `competitorMin_height` directly destructs the original all-positive-j `competitorFiber` witness, reduces its actual long-side point with `exists_minimalFiber_le`, uses coordinate inequalities from `forbiddenStart_le`, and identifies the forbidden start by `Minimal.eq_of_le`. The final `minimalPoint_height` / `forbiddenStart_height` bound uses j>=1 without a stopping theorem or coprimality of m,u. `competitor_zero_column` takes j=u and coreHeight<=u-2, then uses the same carry_u/minimalFiber_budget resources. The signed-then-clamped definition and exact `actualDeadFiber_eq_inter` are unchanged. |
| Antipodal first row | `antipodal_integer_payment` proves the rational strict next-integer gap uniformly for h>=4. The actual consumer retains its exact statement and actual core/endpoint bound, weak surjective actual coreP bound, QCore first-third estimate, original R+2h<=W and W<=h^2. There is no h=4/5 split or call to `five_wordVolume_eight`, exact presentation/P/W formula, or Betti transport. The weak bound's normal-form/surjective-basis proof was read; it does not require t to be a unit modulo 2h. |
| Non-antipodal first row | One rational integer-payment lemma handles u>=8 using the original fourth-volume estimate and the existing mod-3 volume remainder. No u=8..11 refund branch remains in the actual first-row proof. Retaining the volume remainder's own residue arithmetic is consistent with the order. |
| Five/sparse higher rows | `higher_capacity_from_second` assumes the same rational B's row-two capacity inequality, not an actual beta2 conclusion. It divides only by positive choose(e,2) and choose(e,i), including i=e. The actual wrapper obtains the additive package from `actual_positive_rows_add`, uses the same B for coreP and Rhat+u, and uses Pascal over rational casts. It does not call actual five/sparse higher or a final comparison. Five uses B=14 at u=8 (resource row-two demand 104<=112), B=u^2/4 at u>=9 with the exact positive cubic gap, and preserves source vanishing above five. It does not call either choose-quadratic theorem. Sparse passes B=W and the existing `sparse_second_payment`; `actual_sparse_resource_add` is retained unchanged. |
| Dense | The new helper chooses one lex quotient L and one K, then simultaneously returns every positive core-row bound and the t=2 / t>=3 correction implications. Its quantified t<=q range still includes t=0,1. At t>=3 it uses r=t uniformly, not a t=3-specific correction. The gamma/coefficient proof includes q=4,t=3 with non-strict comparison. The new payment calls neither old payment nor old large-coefficient lemma; its proof never divides by a possibly-zero binomial. The actual consumer directly calls the new same-K helper and the new two payment branches. Old public resource/payment/coefficient statements are retained as compatibility exports. q=3 resources are unchanged. |

All actual consumer statements retain arbitrary `(k : Type) [Field k]`; divisions introduced by the new arguments occur in Q. Internal core variables `D.a` and full variables `D.Variables` remain distinct. Existing normalization/comparison chains still end at the same actual completed source and literal interval-completion target, each with its own `AtomExponent`. First/above-top handling remains in the existing all-row comparisons. The frozen W_FIVE/W_SPARSE/W_DENSE/W_CLOSE chains were read through their unchanged closed-goal proofs; this is a source connection observation, not a claim that frozen fixtures were rerun.

## Compatibility and import checks

A read-only source-header comparison against the baseline found all **57 baseline declarations** in the eleven modified production files present with identical comment/whitespace-normalized statement headers. Their enclosing variables and namespaces are unchanged in the diffs. This is a static statement-preservation check; compiled normal and explicit types remain verifier scope.

An independent recursive traversal of source import lines found:

- RowPackage: 477 reached module names, no Endpoint.Stopping.
- SocleBounds: 401 reached module names, no Endpoint.Stopping.
- Width.Closure: 715 reached module names, no Endpoint.Stopping.
- FiniteCompetitors: 416 reached module names, includes Endpoint.Stopping intentionally.

Traversal stops when an imported module has no local source; module counts include those terminal names. The two new production modules are explicitly appended to the umbrella with the old umbrella prefix preserved. HigherFromSecond's imports go down to NormalizedCapacity and PositiveRows; neither actual higher consumer nor final comparison is imported back into it. Source-level root checks and supporting proof-body reading were kept distinct from import reachability and axiom checking.

`audit/run18/RequestedGoals.lean` SHA256 is the required `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`.

## Exact boundary fixture coverage

- Endpoint: literal all-positive-length equivalence, unrestricted j witnesses, finite minima/height/pure-v API, small-height boundary, retained finite computational API, and m=6,u=3 noncoprime example with j=37 beyond the stopping bound.
- Integer payment: APD h=4 actual first row; APD h=5,t=2,u=10 with an explicit nonunit check; actual statements over arbitrary fields plus Q/F2/F3 instances; arithmetic first-row examples including all four formerly split non-AP widths.
- Higher: e=2,u=2,B=2; e=5,u=8,B=14; e=5,u=9,B=81/4; each quantified over all rows 2..e and explicitly instantiated at the top row.
- Dense: gamma=0 and payment equality at q=4,t=3,j=0; new payment on all rows through j=5; general j=q+1 top row; actual q=4,t=3 top row over arbitrary fields; same-K helper statement preserving the full t<=q quantified range.

These fixture bodies directly exercise the intended lemmas/consumers. Their existence and meaning were reviewed; no execution success is asserted here.

## Reviewed content hashes

Hashes were computed from the reviewed bytes after dense/higher implementation agents had completed. Any changed listed file requires renewed review or an explicit determination that the changed scope is outside this report.

| File | SHA256 |
| --- | --- |
| `NSP14/Endpoint/CarrySums.lean` | `9ae46d0698db6b8222d4f01dddd4348087fff6bc722d2a7b9c863540dce90652` |
| `NSP14/Endpoint/CompetitorBounds.lean` | `5265a086da0725401d61e5bf53224e1ebc3a05b006be4503bb6b83c62b6c8434` |
| `NSP14/Endpoint/FiniteCompetitors.lean` | `321449ac5b14fd26300c24835b255f30c02cc7d0e810f78f3b5b57fc351cfe03` |
| `NSP14/Endpoint/FiniteSocleBounds.lean` | `93ca2260b37fcdfbaf75554be0b440e1ec922bf2fc30ce105aa78847169c810d` |
| `NSP14/Width/AntipodalComparison.lean` | `a40398b76d2cb496b4560ccd3f14dc94ddf37465a0b06f6418660b3d64497ebf` |
| `NSP14/Width/FiveNonAntipodal.lean` | `4c7c11d7607edc96c3941a828a9f74a6af1ffbdb75fa2ac3abec7355ea32a2d9` |
| `NSP14/Width/FiveHigher.lean` | `436d9a80d69bc7f3155928a61c99878186fa2b6aa4056ad64043efd1652218e7` |
| `NSP14/Width/SparseHigher.lean` | `a704ea674e854d22c0834eb3fa17f3c993c0e03df4c1cbe6bdcc20950442db62` |
| `NSP14/Width/DenseLexResources.lean` | `9bdb0a81d44f6cd5d17986ac02ebc691193051d80e2738177395388b8f993dfc` |
| `NSP14/Width/DensePayment.lean` | `b529aedf9436a619b4377fc71865e2d4291f2e0d83c19994dfd2d8f15aeb3b5a` |
| `NSP14/Width/DenseComparison.lean` | `7de7522543967f98568924765c2351fbbf599b75340f1bb29762e3d977a165ab` |
| `NSP14/Width/IntegerPayment.lean` | `f7def4a993c944eb676615fa169d73655798fe2731723f2eb0cf240c8b49a9f5` |
| `NSP14/Width/HigherFromSecond.lean` | `a4126435ebc5829e99c0404dd0082bbff0b473ea43c7fd710adf368e3304b0a8` |
| `tests/V06Endpoint.lean` | `588ad3b1f7583cb552d8351960eddc128b90ebc22f707dd684fa7028345418f0` |
| `tests/V06IntegerPayment.lean` | `8151aa47eb6b83224591c11e9d78abff3be92b606b317bb9559739476a8db5fb` |
| `tests/V06HigherFromSecond.lean` | `5165c893c8dabdfc92d98520f95e149ee120e40079784badf220b7d487832398` |
| `tests/V06Dense.lean` | `747db30695235e0db7784b667adf46273d05a12b0159bcbb645451966dcb4423` |
| `audit/v06_alignment/RouteChecks.lean` | `7ed0a323b3cc793e10b47c2b847439747466a6c012d0f647730c86913e810418` |
| `NSP14.lean` | `8728efd06c8d891d29557ff62435e71e607ac80ec227589b860d4acc8fdbbf17` |
| `NSP14/Endpoint/ActualKernel.lean` | `9fcb8b751d540d92bd3d0c729109ad1001af913fc44a410d6b74150ad78c9c43` |
| `NSP14/Endpoint/Carry.lean` | `95ba789f8bcdb85db4e7cec6072cf197f1eec1ba532163180d0c8e932d9d0702` |
| `NSP14/Endpoint/PositiveRows.lean` | `ddfe975206ebe65cd579341a3a0a3127295667018b459f4be69a941efe66b9d1` |
| `NSP14/Endpoint/FullTransfer.lean` | `dbe038aa0960263c5008666a5f64dd184220af04a907b019baf37139b2f784f1` |
| `NSP14/Width/AntipodalCore.lean` | `ceaf178f71301a50e6eb3c7ea67d33bee8bad9253d54e1097e62e1a51bc4b80a` |
| `NSP14/Width/FirstResources.lean` | `0d61ddbb80751d3fb6273a62a587a85d2d9717d720cbf57d74741b069089631b` |
| `NSP14/Width/SparseSecond.lean` | `1137372080d07abd9fdbcbfa5827582f283ab383be2792cb24342a94cd917284` |
| `NSP14/Width/NormalizedCapacity.lean` | `001e46887db4c6dfcbc42407dcaed3f27fffcb6705fe40045a6b2574a842de0a` |
| `NSP14/Width/SparseComparison.lean` | `ebe3c2639fa6f01cf86033d0bd23fe0debc022db93bc5ad7108d0c826a9fb15b` |
| `NSP14/Width/FiveComparison.lean` | `07b81150019d368b326bd5447bb89be049ae21e8321f3b8183a6f7d9ae0ff524` |
| `NSP14/Width/Closure.lean` | `23d29bc36ddf482a291d8f81e7f9af9fc28426f7448e47a65c348931876592b0` |
| `audit/run18/RequestedGoals.lean` | `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689` |
| `audit/run18/FiveClosedGoals.lean` | `cdc1809aca59375f9584a6d140e6124f250d69c528306b5a3934ba1561f0c71f` |
| `audit/run18/DenseClosedGoals.lean` | `ed572df4b0df76578b3f70678f34ca7a1b0948f63247bfe3f9f961eda1ab34af` |
| `audit/run18/PartialClosedGoals.lean` | `246d6f440927bfb3f96377f056ef7b54e757a004fe0456940ecc5712c3a58f0c` |
| `audit/run18/ClosedGoals.lean` | `383de8790d28cb0209d355196999ac5c1d1247802e7b93038081b25c306e51db` |
| `docs/superpowers/specs/2026-11-15-v06-alignment-order-input.txt` | `51372b807584acf3cd78d0b022a44658e4bfcdb6ae51db41aaeb43a448dfe66c` |
| `docs/V06_ALIGNMENT_PLAN_JA.md` | `82416a7eaec1181bb1aa5f88fc89b8b9923d097e98970331d24b30c0e71fffdc` |
| `docs/V06_ALIGNMENT_CHANGE_POLICY.json` | `876e70e3508007cc97d0fe887fdf8c08ccf5510095ba5142f93ae0ebcee798cf` |
