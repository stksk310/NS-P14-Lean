# Block10：次数付き環全体とactual x核・head商

Use superpowers:executing-plans inline; one fresh independent final reviewer.

Goal: Block09の実冪の商を全直和の可換環へ組み立て、その基底座標を使いx乗算の核全体とhead商を構成する。
Spec: V02 §2 / V03 O_COORD。係数環は必要な仮定を各定理で明示。完備化比較、N/Qや同jump strata、Torは今回の完成に含めない。

## Tasks

1. 実商の積からgraded monoid/ring axiomsを証明してdirect sum可換環を構成。
2. 全直和と全半群指数の有限支持座標を線型同定し、初期単項式の積を接続。
3. x作用の係数表示と単射なlive shiftから核全体をterminal支持として同定。
4. imageをlive incoming支持へ同定し、cokernel/head商の基底と環のprincipal quotientへの接続を証明。
5. 具体例・旧9Block回帰・全新規宣言の公理依存・前manifest hash・原稿対応・独立レビュー・ZIP・Push。

## Review Focus

次数0、m=1、係数の消去、二つのlive矢印の衝突不在、ringとmoduleの整合性、actual kernel/imageと単なる単項式判定の違い。完備化と代数的半群環を区別し、global T≅Nを主張しない。

## Ledger

Base 1d7c4a8a088ecd37648fa5afeb7c35421e2a6f59. Work branch is already isolated from main; no new worktree needed.
Pre-flight: Task2 consumes actual GCommRing and degreewise equivalences; Tasks3–4 consume global monomial coordinates and multiplication. No conflicting interfaces identified.

Tasks1–4 complete: 7 source files; full commutative k-algebra, global monomial coordinates, full actual kernel/range, principal quotient head basis, basis-vs-actual-class identities and degreewise x-action compatibility.
Ruling: completion comparison and N/Q remain separate; the completed target itself has not been replaced by the algebraic model without a comparison theorem. Full terminal/head bases here do not assert global finiteness of their index sets.
Implementation: explicit named family and ring/algebra instances keep Lean higher-order instance inference stable; all structures reuse the actual quotient operations and existing module structures.

Task5 verification complete: 20/20 commands,323 standard-axiom reports,34 unchanged predecessor hashes. Independent review found no correctness or scope issues; reviewer separately compiled the new tests and checked all34 baseline hashes. No deferred findings.
Publication: manifest and audit ZIP are prepared next; authorized ordinary commit/push to work, followed by remote SHA and clean-worktree verification. No destructive operation or merge is needed.
