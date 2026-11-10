# Block11：actual N/Q、Apéry基底と次数別計数

Use superpowers:executing-plans inline and one independent final reviewer.

Goal: A=G/xGの非Apéry head空間をactual ideal Nにし、実商Q=A/NのApéry基底と有限次元・次数別計数を構成する。
Spec: V02 §2 / V03 O_COORDの(O1)。Block08の数値計数をactual商へ接続する。

## Tasks

1. Aの単項式と任意の有限和の積を扱い、非Apéry支持空間がA全体のidealであることを証明。
2. actual Nの非Apéry head基底と、actual Q=A/NのApéry係数同値・基底を構成。
3. actual quotient写像で各次数の像を同定し、finrank Q=m、q0=1、q1=e−1、q2≤δ、上次数≤δ+1と高次総量を接続。
4. 退化境界・非零NとQでの消去・旧10Block回帰・全公理依存・独立レビュー・原稿記録・ZIP・Push。

## Review Focus

Nの安定性は全Aによる乗算。零になる積とheadでない積、Apéry性の下方閉包、任意の係数の和、m=1、次数0、actual quotientからの次数像。完備化比較・jump strata・Torまでを主張せず、global T≅Nも主張しない。

## Ledger

Base 791a2c94eda09479d0582f30726669c6d28fbc7b. Existing work branch is isolated from main.
Pre-flight: Task1 uses Block10 actual monomial bases and product. Task2 uses Task1 ideal and coefficient projection kernel. Task3 must identify inherited degree images, not merely assign a convenient grading to the coordinate model.

Tasks1–3 complete. Scope extended within the same O_COORD milestone to registered gradings on A and Q, mathlib N.IsHomogeneous, actual degree-one atom generation, Artinian Q, and the exact top degree ν. All use the same quotient constructions.
Ruling: qDegree and headDegree are defined as actual images of G components before proving their coordinate description; neither is assigned a model grading by definition. N stability is proved for all A elements.
Ruling: length Q=m is recorded as total k-dimension. Generic Module.length identification, completion comparison, jump strata and global A・N・T finiteness remain explicit separate obligations.
Task4 implementation verification complete:26/26 commands,443 allowed-axiom reports,42 unchanged predecessor hashes. Independent review and publication follow.

Task4 verification and review complete: independent review found no correctness/scope issues and separately checked tests,42 baseline hashes and120 report names. Added test-only ordinary m=e=3 boundary; final26-command run passed with443 allowed-axiom reports. No mathematical source changes after review; no deferred findings.
Publication: prepare the manifest and audit archive, commit/push to work under standing authorization, then verify remote SHA and clean worktree. No merge or destructive operation.
