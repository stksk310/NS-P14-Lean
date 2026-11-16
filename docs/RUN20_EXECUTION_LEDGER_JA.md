# Run20 実行台帳

Plan: docs/superpowers/plans/2026-11-15-run20-v06-main-closure-order.md
Base: 07fe1ed952ae31ce01255ce53df538bf0a76d5cc

Inline実行。小補題・内部commit・時間・contextで終了せず、Task1–9から全検証・独立レビュー・不変ZIP・通常Pushまで続行する。

Ruling: 共有workspaceの.git read-onlyと先行証跡保持のため独立dissociated checkoutを使う。旧source/HEAD/cacheへの影響を避ける。誤っていれば先行認証を無効化するため、donor source identityとcacheコピー範囲を検査する。

Ruling: cloud skillのshell helper資産が取得不能なので、同じplan identity・各Taskのbrief/BASE・RED/GREEN・commitを専用ignored ledgerへ記録する。未取得のskill本文はなく、作業の停止理由としない。誤っていればtask記録が欠落するためGitとtracked台帳にも対応を残す。

Task1 in progress: 最新work 07fe1ed、AGENTSなし、dirtyなし、追加監査修正なし。正確なRun19 provenanceと実export型を再確認する。

## Task 2 / frozen contract
I_PARTITION includes six regions, actual cut facts (the stronger all-e≥4 scope), and actual narrow normalization. Predicate definitions were introduced before their proofs to freeze the precise statement. I_MAIN is all S/k/i and the literal all-S target. Both named acceptances failed only for the absent closure export; definitions/target contracts passed. The immutable policy commit is bcadd3b.

## Tasks 3–7 / mathematical connection

- Six-region exhaustive and exclusive partition, actual rank facts including r2/delta0, and physical narrow normalization are proved in Main.Partition. Predicate definitions preceded proofs only to freeze the contract; no comparison was placed in a partition premise.
- Carrier equality transports actual Betti with each ring's own variables, then completed_totalBetti on both sides. A different conductor fixture tests this distinction.
- Five production branch consumers and a six-region Main proof close all S/k/i; e1 is the literal [1,1] closure. The old target has a separate he>=2 compatibility corollary.
- Frozen RED exports became GREEN. Actual examples cover Q/F2/F3 and physical/nonCM/five/edge/dense/sparse boundaries. <6,7,9,11> has source beta5=0 and target beta5=5 by the actual AP formula.
- Early preflight failures (proof elaboration of Nat subtraction/let aliases, missing explicit theorem types, missing AP-width import, and fixture instance heartbeats) were repaired without changing mathematical scope; failed logs remain in provenance. Named proof types are explicit, no defProp warnings are accepted in final validation.
- Fifty original ID statements/quantifiers are retained in the coverage JSON with production declaration groups and actual consumer modules. Sufficient alternative proofs and unnecessary stronger assertions are explicitly distinguished. No required mathematical input remains assumed.

## Tasks 8–9 / frozen publication protocol

Full current and immutable-base audits import all every production/test/audit module directly. An independent environment name inventory detects even one dropped private declaration. All Run19 318 checks/299 fixtures remain, historical policy guards replay at their own immutable snapshots, while mathematics and new Main tests use current source. Normal/explicit types and collectAxioms cover every project declaration; allowed axioms are exactly propext/Classical.choice/Quot.sound.

The final source snapshot must be committed before cold verification. Validation is not publication completion. Review, package, normal Push, actual remote SHA and clean status are separately observed and bound as post-validation Git bytes. Source-bound docs stay unchanged after verification.

事前検査: root build 6706 jobs成功、全新規fixture/必要依存はexit0・警告0まで再実行。整数分割81640ケース・AP profile41552行、Mainからの10個別根とV06/Run19根を検査。新guardは実Lean axiom injectionを含む45controlsでPASS。初回symlink拒否の診断形式不備を修正し、失敗ログはpreflight_20261116_01に保持した。全型監査のimportだけを切り離したprobeもPASSし、実行時間の主因は通常/explicit型と全宣言公理列挙である。

全宣言名の独立一覧は15774件。Array走査版とHashSet版の実Lean出力が完全一致し、HashSet版は28.406秒で完了した。型/公理列挙を4分割・最大3workerへ並列化する。各partも全project moduleを直接import allし、実collectAxioms/normal/explicitを宣言ごとに行う。partのmodule集合と宣言名の和集合・重複を検査し、独立固定一覧と再照合する。対象を減らす高速化ではない。
