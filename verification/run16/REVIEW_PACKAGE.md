# Run16 whole-branch fresh-context review package

Base: 447b7ae782414b739968a2a3009dd3a52ae230d0. End commit is supplied in the reviewer invocation.

Read-only review. Do not mutate worktree/index/HEAD; do not dispatch any subagents. Review the whole Run16 range, in passes if necessary. The source and tests are Lean kernel proofs, so inspect actual exported hypotheses and connections in addition to absence of sorry.

Requirements: docs/superpowers/plans/2026-11-10-run16-endpoint-kernel-transfer-order.md (requested exact commit0cda4e8), user authorization to use improved proofs if paper correspondence is recorded. Run15 baseline is fully closed; predecessor evidence is frozen.

Primary guide: docs/RUN16_AUDIT_HANDOFF_JA.md. Exact contracts: audit/run16/ClosedGoals.lean. Canonical entry: NSP14/Endpoint/RowPackage.lean. Detailed11ID map and proof-route changes: docs/RUN16_PAPER_CORRESPONDENCE_JA.md. Decisions: all Ruling lines in docs/RUN16_EXECUTION_LEDGER_JA.md. General Artin proof deliberately reuses the already proved actual standard-module harmonic j1 theorem instead of duplicating parent/child counting; evaluate the actual hypotheses/conclusions, not filenames. idealGeneratorNumber uses actual ideal Tor0/Nakayama fibre, with actual connecting iso; do not infer a separately implemented arbitrary nonhomogeneous generator algorithm from the name.

Validation: verification/run16/final/verification.json and all named normal/explicit-type audit declarations. All new accepted anonymous examples were made named theorems so their types survive in the Lean environment; previous failed metadata aggregation is retained under final_attempt_anonymous, not labeled final PASS. Actual PC/PG/R triples and char2 are proved; finite799-case model is separate evidence.

Review all11 obligations and exported original-source completed bounds, assumptions, finite-k use, zero/top rows, graded actual actions, exact kernel/all-j stopping, R versus sigma, arbitrary-characteristic minor, actual q2 monomiality. Check verifier/package reproducibility and source/evidence binding. Point out any overclaim or missing required mathematical bridge. For every finding provide severity, file:line, impact and a concrete correction. Explicitly list behaviors declined to judge (or say none). Do not claim issues on files you did not inspect; say which passes/scope you examined.

## Review Focus

1. **同じsourceと三つの環を保つ。** 全環Sはq+2変数、端点Eは2変数、内部Tはq変数。coreは仮想の別半群への置換ではない。剰余分解はE加群同型であり、環の直積でも内部T加群の成分別分解でもない。
2. **EHの範囲を縮めない。** `0<a₁<…<a_q<u<m`、q≥2、d≥1、gcd(a₁,…,a_q,u)=gcd(m,d)=1。必要なのはu<mでありdu<mではない。gcd(m,u)=1、Cohen–Macaulay性、d=1を追加しない。
3. **kernelと商を区別する。** actual kernelは`N_s=M_s∩T_s`。全j≥1を停止式で尽くす。`Q_C→Q_G`のkernelは一般に非零であり、Betti単調性や`P_C=P_G`を仮定しない。
4. **有限性の場所を守る。** GはE有限生成・rank 0であるが、一般にk有限次元ではない。有限なのは端点homologyとQ_C/Q_G等。Gに有限長Eulerを適用しない。与えられた`MinimalFreeTower`の比較だけで任意対象への存在も済んだとしない。
5. **添字・向き・標数を守る。** 負添字の二項係数は0。Natの`i-1`を無条件に使うとi=0で誤るため、guard又はInt添字で定義する。差・floorは整数/有理数で扱うか非負性を先に証明する。carryとheightは同じ向きのcoreに属する。有理重みを正標数の体内で割らない。

