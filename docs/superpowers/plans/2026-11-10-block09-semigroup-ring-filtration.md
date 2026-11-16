# Block09 半群環・冪フィルトレーション・次数付き商

Use superpowers:executing-plans inline, followed by one independent review.

Goal: Block08のactual orderを代数的半群環k[S]の正元イデアルの冪と同定し、次数nの商をorder=nの有限支持座標へ同定する。
Spec: V02 §2 / V03 O_COORD。完備半群環との接続は別の定理として残す。

## Tasks

1. 半群環と係数で定義するorderフィルトレーションを構成し、積・降下性を証明。
2. 正元単項式生成イデアルと第1層を同定。正元表示を使い全ての冪を同定。
3. 各層からorder=nの係数抽出を定義し、核=次層・全射・商線型同値を証明。
4. 退化境界と単項式のlive/killed判定、旧8Block回帰、公理依存、独立レビュー、原稿台帳、ZIP、Push。

## Review Focus

n=0、x=0、multiplicity=1、零係数、係数環の仮定、商の分母が実際の次冪であること。
代数的半群環と完備半群環を混同しない。全直和の環同型やTorまでを主張しない。

## Ledger

Base ae53ad026a55a663bfb295866317d30f8aa72fd3. Existing work branch is isolated from main.
Pre-flight: Task2 uses Task1 coefficient criterion; Task3 uses Task2 equality of ideals.
Ruling: associated graded is first formalized degree by degree as quotient vector spaces. Completion and assembly of the full direct-sum algebra remain explicit future obligations; this keeps the boundary reviewable.

Tasks 1–3 complete: actual ideal powers, coefficient quotient, finite monomial bases and bilinear quotient product. Added atom-span/maximality and xAction to close the numerical/algebraic boundary.
Task 4 verification complete: scripts/verify_block09.py passed 19/19 commands,252 axiom reports,26 predecessor hashes. Independent mathematical review passed. Two documentation hypotheses corrected to match the Lean types; no proof-body changes.
The basis finiteness proof uses the coarse conductor bound v<(n+1)(C+1); no minimal conductor or unproved Hilbert finiteness input is needed.

Final: Ruling: review labels for the two prose hypothesis omissions were raised from minor to important documentation precision, since the arbitrary-CommRing introduction could otherwise overstate nonvanishing/maximality. Local qualifications were added; no mathematical assumptions changed.
Final: fixed documentation scope — recorded RED→GREEN wording checks and reran the entire 19-command suite. No deferred findings.
Task 4 complete: verification and independent review saved; archive and manifest prepared for the authorized ordinary push to work. Remote SHA and clean worktree will be checked after push.
