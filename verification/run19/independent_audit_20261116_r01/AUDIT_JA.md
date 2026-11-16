# Run19 独立監査（2026-11-16 JST）

対象: `07fe1ed952ae31ce01255ce53df538bf0a76d5cc`（Run19公開・完了記録まで）。実装時の既存レビューを根拠として採用せず、数学の再読、固定snapshotでのcold再検証、保存済み証拠とGit/ZIPの独立照合を行った。

## 判定

**PASS（公開ガードのImportant 1件は修正済み、未解消指摘0）。**

数学の読解監査・独立cold再検証とも10契約すべてPASS。公開packagerのreviewed sourceをGitに結び付けるガードにImportantを1件発見し、最小修正と回帰テストを追加した。

## 数学・契約

`N_DISTANCE / N_WORDS / N_HIGH / N_FIRST / N_SMALL / N_WIDTH4 / N_CLOSE / I_BASE / X_LTV / I_THREE`を確認。`audit/run19/RequestedGoals.lean`は初期凍結e13d8d1から不変（Git blob `3169dbefcda5762b7bc3b14896f89cc7002e29c1`）。元のSのcompleted tangent algebraとliteral interval completionを、それぞれ自身の最小変数で比較する契約が保持されている。CM、actualP=coreP、gcd(m,u)=1、標数制限、有限m上限、結論そのものの追加仮定はない。

N4側は同じactual QCoreの標準語・socle三角形、SCによる純語/混合語評価、元の向きのheight、新cubic、全高次行、corner除去の切り捨てを守った第一行評価、小幅の被覆を再読した。幅4例外では全j競合の両座標とstrict weightによるnormal formからactual kernelを同定し、actual Tor1へ接続する別証明が元の契約を満たす。一般のinitial ideal定理や全生成族の最小性を証明したとは扱っていない。

小embedding側は幅0のliteral target、cofinite witnessに依存しないtransport、e<=2の全行、q>=1 endpoint port、actual QC→QGの核次元による補正、all-j競合のweighted injection、元のR、P_C<=uとR<=C(u-3,2)、e=3のnarrow/full AP/wideの全場合を再読した。X_LTVは初期契約の必要比較命題であり、原論文のより強い3本の線形評価まで形式化したとは扱わない。

独立読解担当の範囲・根拠・有限sanity probeは `N4_MATH_REVIEW.md` と `SMALL_EMBEDDING_MATH_REVIEW.md` に保存する。これらはLean実行結果を代替しない。

## 独立cold再検証

固定HEAD `07fe1ed`で以下を実行。実行中はHEAD/source/既存証拠を変更しなかった。

```sh
PATH=/workspace/audit-tools/lean-4.36.0-rc2-linux/bin:$PATH python3 scripts/verify_run19.py --fresh-test-cache --output-dir verification/run19/runs/independent_audit_20261116_r01
```

プロジェクト全体のlib/IR/test/audit cacheを退避して再構築した。固定mathlib cacheは保持した。318項目・299 fixture・12,792宣言、48 typed module / 2,201 typed declaration / 28 canonical helperがすべて通過した。旧公開型は保存され、依存公理は`Classical.choice / Quot.sound / propext`のみ。終了コード0。独立crosscheckで全source/evidence/Git bytesと既存証拠9,134件も再照合した。hashは`audit.json`と`fresh_crosscheck.json`に記録した。source manifestは公開済みR03と1,581件すべて一致する。再検証で生成する`run19_complete:false`は公開前の検証段階を示すもので、既存R03の公開完了receiptを上書きしない。

## 保存済みR03の独立照合

`published_bindings.json`のとおり、source 1,581件をproof commit `7c6821ee0f43869b2a9b5d9b1b72b8d7a045b4a7`とreviewed commit `c12fbfa66fb7585af013b8bcc4da4fa7ca34fdbe`の両方のGit blobへ照合した。evidence 373件のhash/完全fileset、raw環境出力と保存済み全12,792宣言、全318コマンド/299 fixture、review本文・receiptも照合した。ZIP 1,959 entryは重複なし、CRCと全payload hashが一致する。

既存ZIP: `artifacts/NS_P14_LEAN_RUN19_COMPLETE_20261116_R03.zip`

SHA256: `e14c8616cb0379a4f0063da6f329580fd13cca6f0644f637bca0f7ace890a6bc`

## Important 1: reviewed commitのsource binding不足

発見時の`package_run19_audit.checked_payload`は現在のsourceとproof commit、およびreviewed commitのevidenceを照合するが、reviewed commit内のsourceは照合しなかった。そのため、source Aを証明し、source Bと同じevidenceを含むcommitをreview対象に指定し、その後source Aに戻すと、異なるsourceのreviewを受理できた。独立の使い捨てGit repoで受理を再現し、受理を拒否すべき回帰テストが実際に失敗することを確認した。

既存R03では全sourceがreviewed commitと実際に一致しており、今回のZIP・数学的証明への不整合はない。この指摘は公開手続きのガード不足である。

最小修正: 同じsource manifestの各hashをreviewed commitのGit bytesにも照合する。実Git/実packagerを使うsource-substitution負例を追加する。修正前は回帰負例が`invalid input accepted`で失敗（exit 1）。修正後は実packagerの正常公開例・差し替え拒否を含む35 controlsがPASS（exit 0）。変更policyのpreflightもPASS。修正案の独立読解レビューは指摘なし（`GUARD_FIX_REVIEW.md`）。

cold再検証の対象は修正前の07fe1ed。後続の修正はPythonの公開ガードとその負例だけで、数学的Lean sourceは変えない。既存R03のverification/review/completion receipt、ZIPは不変とし、新しい証明ZIPの再認証は主張しない。

## 範囲

これはRun19の10契約に対する監査である。全P14の最終合成I_PARTITION / I_MAINはRun20に残る。強いLTV線形評価、一般initial-ideal定理、mathlib自体のcold再構築、完全offline checkoutは今回の完了主張に含めない。

## 再現資料

`audit.json`に検証hashと修正scopeを、`guard_suite_red.log` / `guard_suite_green.log`にRED→GREENを保存した。cold検証の全証拠は`verification/run19/runs/independent_audit_20261116_r01/`、修正後の35 controlsは`verification/run19/runs/independent_guard_fix_20261116_green.json`。このディレクトリのPython crosscheck/RED probeは固定workspace pathを持つ当時の監査記録であり、指定した凍結checkoutで実行する。継続利用する回帰テストは`./scripts/check_run19_guards.py`へ追加済み。
