# V06同期 引継ぎ入口

baseは a7504eea25f02728d1be6cd0082e8484d639dbe2。今回の実装内容・公開API・原稿への反映は [対応台帳](V06_ALIGNMENT_LEDGER_JA.md)、有限変更範囲は [変更規則](V06_ALIGNMENT_CHANGE_POLICY.json)、実施項目は [計画](V06_ALIGNMENT_PLAN_JA.md)。指令本文はbaseに保存済みの `docs/superpowers/specs/2026-11-15-v06-alignment-order-input.txt`。

最新の認証は新規 `verification/run18/runs/v06_alignment_*/verification.json` のstatusとproof_snapshot_commit、同じディレクトリのSOURCE_SHA256/MANIFEST_SHA256/COMMAND_MAP/snapshotおよびreviewのbindingを確認する。この文書の存在や旧Run18 COMPLETEだけを新経路の認証として扱わない。

実行入口：

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python scripts/verify_v06_alignment.py \
  --fresh-project-cache \
  --baseline-cache /tmp/ns-p14-run18-final-audit-20261115/.lake/build \
  --output-dir verification/run18/runs/v06_alignment_<UTC>_<unique>
```

baseline-cacheは任意の高速化で、donorのbase production/pin一致を検査し、コピー先の隔離baseでビルドして公開型を得る。省略時も隔離baseを作って検証する。新出力先は未存在・相対・V06専用prefix必須。旧R16などを渡して上書きしない。

新packageも専用スクリプトでsource/evidence/reviewとGit snapshotの一致を確認してから一意なZIPを作る。最終的なproof/evidence/review commitとZIPのhashは配布receiptに保存する。旧Run18 ZIPとreceiptは不変。

Root別の経路要件は `scripts/check_v06_routes.py` と `audit/v06_alignment/RouteChecks.lean`。元の全j kernel、PC/PG、actual R/Hx、元Sとliteral interval target、任意体、各環自身の最小表示、0/top/above-top行を保持する。強い独立定理と停止による有限計算APIは引き続き利用できる。

V06同期はRun19ではない。次のRun19は既存計画とそのsource gatesに従う別作業とし、N4や全P14が今回完成したとは宣言しない。
