# Run15 final closure review

Read-only whole-feature review required by the requesting-code-review skill.
The prior first-checkpoint review did not certify the subsequently proved goals.

Source baseline: `20aadbf7011692eb3bfffef49029e2c5e416ef3d` (Run14 with reproduction repair).
Immediate final-delta baseline: `33079c170d038eddb432584837035566ae3577ae`.
Review head is recorded in the fresh reviewer request and final review report.

Read the complete order:
`docs/superpowers/plans/2026-11-10-run15-actual-tor-target-ordinary-order.md`.
Inspect whole Run15 in passes and distinguish inherited checked source/evidence from
the final 25 production modules plus 4 tests and exact original-goal closure audit.
No need to duplicate the full verifier; independently inspect its coverage and types.

Entry points:

- `audit/run15/RemainingGoals.lean`: frozen original eight proposition definitions.
- `audit/run15_closure/ClosedGoals.lean`: exact proofs of all eight, no new premises.
- `NSP14/ArithmeticSequence/BettiFormula.lean`, `ModelTorClosure.lean`,
  `ModelKernelDivision.lean`, `ModelKernelBetti.lean`, `WindowBetti.lean`:
  final AP actual-object assembly and Tor vanishing via x-factorization.
- `NSP14/Homological/QuotientBettiAdditivity.lean`, `KoszulVariableMaps.lean`:
  actual LES ranks and null-homotopy. Infinite k-chains, finite homology only.
- `NSP14/Ordinary/Closure.lean`, `NumericalBettiClosure.lean`,
  `IntrinsicFullTransfer.lean`, `RelativeRowsAll.lean`: ordinary all-row closure.
- `NSP14/Target/IntervalAPBetti.lean`, `IntervalBetti.lean`:
  literal minimal interval target, completed-cone formula including row zero.
- `docs/RUN15_CLOSURE_LEDGER_JA.md`, `RUN15_REMAINING_DECLARATIONS_JA.md`,
  `LEAN_PAPER_ALIGNMENT_JA.md` A55–A72: actual premise supply and replacement proofs.
- `scripts/verify_run15_closure.py`, `package_run15_closure_audit.py`:
  frozen baseline, fixture dependency order, empty test cache, all tests/numerics,
  Lean environment axiom scan and normal/explicit types for the entire Run15 delta.

At review start the status is PROOFS_CLOSED_PENDING_FINAL_AUDIT, not a claim that
final evidence or remote publication already exists. The final verifier independently validates mathematical closure; the packager
requires COMPLETE publication status and a separate final review PASS. Old PARTIAL documents and ZIPs are
historical immutable checkpoints; use the current remaining-goals registry.

Check original arbitrary fields (including characteristic 2), genuine general d,
minimal atom counts, P/R/full-variable separation, H0/top/zero boundaries,
same witness/cut/tower/resource, exact original goal types, actual completion,
absence of hidden comparison or rank inputs, no k-finite G/J assumption,
and honestly delimited Run16–20 scope. Report concrete Critical/Important/Minor
findings, every declined-to-judge behavior with reason, and a clear verdict.

Do not change checkout/index/HEAD or dispatch further agents. Final ZIP, normal
Push and remote-SHA/clean confirmation will be performed by the primary agent.
