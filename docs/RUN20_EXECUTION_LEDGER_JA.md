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

### 型表示の計測と採用形式

標準pp.explicitの二つのprivate補題は表示だけに約19秒/11秒（CPU競合下では40秒/19秒）を要した。実collectAxiomsは0–1ms。notationだけ・proof表示だけの変更は十分でなかった。Lean標準のpp.allをexplicit側へ採用し、coercion・universe・完全修飾名・proof引数まで表示する。通常型は従来のMeta.ppExprを保持。これは型/premise/行/宣言被覆の縮小ではなく、よりexplicitな表示形式である。Mainの旧標準explicit記録も保持し、新しいfully-explicit期待型を別ファイルへ保存した。実証明と凍結契約は不変。

表示処理の旧preflightは `audit_display_transition_20261116_01/cancelled_processes.json` にSIGTERM/実commandを保存し、検証成功へ数えない。旧sourceと部分ログは保持。新preflight/最終cold検証は同一の完全explicitモードでbaseと現sourceの全公開型を比較する。part間のmodule/宣言重複・欠落、独立15,774名、同じ全private import環境を検査する。

### 最終の全型記録方式（前項pp.allだけの方式を置換）

pp.allでも複雑な型の表示に秒単位を要したため、全宣言のexplicit欄はLean標準Expr.dbgToStringによる完全なkernel型へ切り替えた。通常欄はMeta.ppExpr、元のkernel型も別欄、Main三出口は標準pp.allのpretty-explicitも併記する。測定例は163217文字を22msで出力し、表示省略は0。宣言/argument/universe/instance/proof項を減らさない。

再現比較用のbinder名は深さごとに一意の名前へalpha正規化し、各元型との実Expr.eqvを全宣言で検査する。binderInfo・変数index・定数・universe・metadataを保持する。予約binder名と実定数の衝突も拒否。変数の入替え/implicit種別/universe/200段の項/metadataを含む9実Lean controlsをPASSした。初回のmetadata削除は実roundtrip検査で拒否され、正確に保持する実装へ修正した。初期smokeのtoString記法・controlの予約語も診断どおり修正し、失敗ログを保持する。

重いpretty専用preflightは二つのdisplay_transition receiptにSIGTERMと実commandを記録して置換し、成功checkに数えない。最終coldは全型を同じ完全kernel形式で採用baseと比較する。これは数学的証明や契約の変更ではなく、従来pretty出力のproof/depth省略を補う、検査可能な完全型記録である。

### メモリ上限の実測と最終DAG記録

展開文字列版の並列preflightは16GiB上限に達し、4プロセスがexit137で終了した。memory.eventsと全command、継続中jobの停止をaudit_memory_transitionに保存し、成功へ数えない。型は共有部分を参照するLean.Expr.DAG.v1へ変更。Nameのstr/num成分、全universe、全binderInfo、bvar index、let依存フラグ、literal、projection、metadata参照を保持する。各JSON nodeを実際にdecodeして元Exprとの厳密ExprStructEqを検査し、canonical型はさらに元型とalpha同値を検査する。metadataの診断snapshotも同梱する。

通常型はMeta.ppExpr + fresh cache、Mainは標準pretty-explicitも併記。出力は逐次JSONLへ保存し、完全なbytesをgzipへ移す（未圧縮SHAも記録）。一つの監査は8part/最大2workerとする。DAG版は約5GiBで複数partがPASSし、全プロジェクトのscopeは保持した。旧失敗出力を変更せず、新一意出力先で最終coldへ進む。

基準07fe1edの全1003 module・15542宣言が、通常型/完全explicit DAG/実collectAxiomsでPASSした。source SHAはGit base bytesへ全件再照合。golden recordをsource provenanceへ固定し、最終coldでは隔離base再実行との一致も検査する。Rootの全708 production moduleがumbrellaから到達することも確認した。現在は新Mainを含む全1019 moduleの同じ監査へ進む。
