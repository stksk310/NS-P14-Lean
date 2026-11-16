# Run20 実行台帳

Plan: docs/superpowers/plans/2026-11-15-run20-v06-main-closure-order.md
Base: 07fe1ed952ae31ce01255ce53df538bf0a76d5cc

Inline実行。小補題・内部commit・時間・contextで終了せず、Task1–9から全検証・独立レビュー・不変ZIP・通常Pushまで続行する。

Ruling: 共有workspaceの.git read-onlyと先行証跡保持のため独立dissociated checkoutを使う。旧source/HEAD/cacheへの影響を避ける。誤っていれば先行認証を無効化するため、donor source identityとcacheコピー範囲を検査する。

Ruling: cloud skillのshell helper資産が取得不能なので、同じplan identity・各Taskのbrief/BASE・RED/GREEN・commitを専用ignored ledgerへ記録する。未取得のskill本文はなく、作業の停止理由としない。誤っていればtask記録が欠落するためGitとtracked台帳にも対応を残す。

Task1 in progress: 最新work 07fe1ed、AGENTSなし、dirtyなし、追加監査修正なし。正確なRun19 provenanceと実export型を再確認する。

## Task 2 / frozen contract
I_PARTITION includes six regions, actual cut facts (the stronger all-e≥4 scope), and actual narrow normalization. Predicate definitions were introduced before their proofs to freeze the precise statement. I_MAIN is all S/k/i and the literal all-S target. Both named acceptances failed only for the absent closure export; definitions/target contracts passed. The immutable policy commit is bcadd3b.
