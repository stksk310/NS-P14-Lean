# P14 / PLMS manuscript: original for audit

This directory makes the manuscript available across independent Codex/chat
workspaces. Local `/workspace/P14-paper` paths belong to the writing chat and
are not assumed to exist in another environment.

Start from this **original ZIP**, preserved byte-for-byte:

`paper/PLMS/P14_PLMS_Preparation_2026-11-16_v2.zip`

SHA-256:
`7ce0d11f1c3764394189113e5c7a4f2a1a361b3c6a1a1a8ad8fee2dddb08d7cc`

The 57 ZIP entries are also extracted here unchanged. The article is `main.pdf`
(25 pages), with editable `main.tex`, `sections/`, and `references.bib`.
The latest declaration includes **ChatGPT Work / GPT-6.1 Sol / Ultra** for
later-stage proof construction, refinement, integration, and audit, separately
from the Codex use. The author's identity and contact details are
included as instructed by the author.

`PUBLICATION_MANIFEST.json` records hashes of the original ZIP and extracted
files. `notes/DRAFT_VALIDATION.json` records the preparation checks.
Whitespace already present in the original notes and pinned Lean excerpts is
preserved so that the extracted files retain their recorded hashes.
`submission/PLMS-checklist.md` distinguishes completed preparation from pending
final mathematical audit and fresh Lean replay. The Lean source release and
proof snapshot are pinned inside the article and reproduction instructions;
this manuscript publication does not alter the Lean theorem.

## Access from another checkout

Fetch `work` and inspect or extract `paper/PLMS/` from that ref. For a fixed
audit target, use the publication commit linked in the writing chat's Push
report instead of a moving branch tip. Existing local edits can be kept while
extracting the folder with `git archive` into a separate audit directory.

## Audit outputs

Preserve the original ZIP and sources. Write any revised manuscript and
severity-ranked referee report to a separate directory, identify the exact
input commit/ZIP hash, and distinguish checked claims from unchecked ones.
The manuscript claims the P14 tangent-cone comparison and the explicitly proved
CMS width corollary; it does not collectively claim resolutions of P7–P15.
The manuscript's original AI-assisted audit rounds are not independent human
referee reports.
