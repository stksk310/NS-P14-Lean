# Public release implementation plan

> **For agentic workers:** Use superpowers:executing-plans inline. The user explicitly authorized GitHub Release publication, Zenodo preservation, and DOI issuance.

**Goal:** Publish the audited P14 formalization as v1.0.0 and verify the resulting Zenodo record.

**Architecture:** Preserve the audited `e72713965716d7f93f672034c6332a79b59b1c53` tree, update publication documents, and release from main. GitHub Actions supplies its scoped repository token because this workspace cannot reach the Release API. A release helper validates the source and assets, creates a draft, publishes it, and verifies Zenodo's exact archived file bytes before recording a DOI.

**Tech stack:** Git, GitHub Actions/CLI, Python standard library; unittest for the publication helper.

**Spec:** User's current authorization in this chat; identity and licenses previously approved: Keisuke Sato, ORCID 0009-0005-4230-0268, Apache-2.0 software, CC-BY-4.0 authored prose.

## Constraints

- Never modify audited Lean source, fixed dependencies, old verifier code, manuscripts, evidence, or old ZIPs.
- Publication updates do not constitute a new Lean run; cite the exact saved proof/audit commits.
- The new English manuscript is in a separate chat environment; obtain its actual revised ZIP before claiming it is included.
- Use existing Zenodo integration; do not create a duplicate deposit or invent a DOI.
- Keep v1.0.0's tag fixed after publication; later DOI links may be added in a new main commit.

## Review focus

- Changed proof bytes must fail the prepublication check.
- Incorrect archive hashes must fail before public release.
- A Zenodo record for another repository/version must never count as success.
- ZIP entries with altered bytes or missing tracked files must fail verification.
- Rerunning publication must not overwrite published assets or create a second release.

## Tasks

- [ ] Write and run failing tests for baseline preservation, asset hashes, record identity, and archived bytes.
- [ ] Implement the release helper and tag-triggered workflow; validate locally without publishing.
- [ ] Update README, CFF, Zenodo metadata, release notes, and frozen release manifest for completed Run20.
- [ ] Incorporate the supplied final manuscript without claiming its additional corollary is a Lean theorem.
- [ ] Verify existing receipts/manifests/archive hashes and run the new publication tests; request read-only review.
- [ ] Push the release branch, reviewable PR, and main update; tag v1.0.0 to execute publication.
- [ ] Observe Release, workflow, and Zenodo output; record verified DOI and URLs without moving the tag.
