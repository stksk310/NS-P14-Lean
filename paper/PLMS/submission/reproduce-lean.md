# Reproducing the pinned P14 proof

The publication record is at release commit
`a5e122a4d09536b1609c5faa8d419f8faf81671f` in
[stksk310/NS-P14-Lean](https://github.com/stksk310/NS-P14-Lean).
Its completion record names proof snapshot
`1a5c6bac9a4fd38a8bc5d13b4c7372e654466e6e`.
The proof, evidence, audit, and packaging commits have different roles; do not
replace the proof checkout with the latest default-branch tip.

Use a fresh working directory and retain Git history. Install elan and the
toolchain named by `lean-toolchain` (Lean v4.36.0-rc2), then fetch the exact
dependencies from `lake-manifest.json`. The mathlib revision is
`139105d28c7685a154cb3093f79edb2e16708099`.

```sh
git clone https://github.com/stksk310/NS-P14-Lean.git NS-P14-replay
cd NS-P14-replay
git checkout 1a5c6bac9a4fd38a8bc5d13b4c7372e654466e6e
lean --version
```

Obtain the dependency build caches using the cache tooling supplied by the
pinned mathlib checkout, without changing the dependency revisions. Ensure
the pinned `lean` and `lake` executables are on PATH. Then run:

```sh
python3 scripts/verify_run20.py \
  --fresh-project-cache \
  --output-dir verification/run20/runs/independent_new_id
```

Choose an output ID that has not previously been used. The verifier requires
`--fresh-project-cache`; the fixed dependency caches are retained, while the
project library/intermediate-code/test/audit caches are rebuilt. An optional
`--baseline-cache` is supported only for a compatible, source-checked base
checkout. Full repository history is used by historical replay controls.

The official procedure is given in `docs/RUN20_HANDOFF_JA.md` and the
`REPRODUCE.md` generated inside the audit bundle by
`scripts/package_run20_audit.py`. The bundle is not an offline installation
of the compiler or dependencies.

## Existing evidence versus a new run

The release records 335 checks and 311 fixtures as passed for its pinned
proof snapshot. That is archived evidence, not a fresh build by the current
paper-preparation task. A new verification run must preserve its own output,
exit status, environment, source identity, and manifests before the final
clean-replay checklist entry can be marked complete.

The current paper workspace has a TeX compiler but no installed Lean/lake
toolchain or full proof checkout. These reproduction instructions were
checked against the pinned verifier and release packager; they have not
been executed here. No new Lean theorem is needed for the publication
declarations, and the added local-ring width corollary remains a mathematical
consequence with the scope described in the manuscript.
