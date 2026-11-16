# Run13継続：検証と監査入口

基準Run12 `6b8d168`、途中版 `92cbe8f`。途中版の証拠は `verification/block13/` と PARTIAL ZIP に凍結している。
最終判定は `verification.json` と `docs/RUN13_CLOSURE_STATUS.json` を参照する。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_run13_continuation.py
```

通常のLean環境では固定 `lean-toolchain` / `lake-manifest.json` に合う `lake` をPATHへ入れて実行する。
検査対象はroot build、Block01–12の全指定回帰、Run13の全受入ファイル、環境から抽出した全新宣言の公理依存、
固定環境と旧84ファイルのhash、scheduleと過去監査境界である。

`declarations.json` にはLean環境が認識する所属module、種別、通常/explicit型、公理依存を記録する。
constructor/recursor/structure projection/自動生成補助宣言も含める。
固定Lean 4のmodule exportでは、検査済みproofのbodyが`axiomInfo`のstubとしてimportされる場合がある。
種別は`exported_kind`に原形を残し、この場合を`exported_proof_stub`と表示する。
真正の公理判定はLean自身の`collectAxioms`（export時にprivate kernel環境で計算された依存情報を参照）で行う。
新しい数学公理なら自分自身が依存一覧に現れるため、許容3公理以外を拒否する検査と自己依存拒否の両方で落ちる。
ソースの明示的axiom/sorry等の拒否も独立に行う。新しいソース宣言の正規表現だけに依存しない。
匿名exampleは宣言一覧には入らず、そのファイルのコンパイルログで検査する。

許容依存は `propext`・`Classical.choice`・`Quot.sound` のみ。追加数学公理、sorry、native_decideは使わない。
Mは有限P生成でよく、Gのchainがk有限という仮定を加えない。実homology有限性を証明してからBettiを使う。

## 独立レビューへの対応

`docs/RUN13_CONTINUATION_REVIEW_JA.md` にCriticalなし、Important2件を記録。

- universe REDは全suiteのKoszulExactnessログ、修正GREENは `exactness_universe_green.log`。
- actual L側の独立order gradingに対するREDは `actual_graded_base_change_red.log`。
  補強は `GradedScalarComparison` / `GradedScalarKoszul` / `ActualGradedBaseChange`。
  実degree pieceの係数変更と同じtotal comparisonへのinclusion可換式を証明し、五つのactual L gradingへ適用する。
  `actual_graded_base_change_green.log` と全suiteの `ActualGradedBaseChange.log` で検査する。

## 主要な受入

P/(X²)=(1,1,0,…)、n変数残余体のbinomial Betti、自由P、空/1/2変数、標数2、非斉次写像1+Xの自然性、
実G/T/A/N/Q・完成接錐・jumpの変化する半群・同jumpの内部次数差、実L[X]作用とactual係数変更を含む。
原稿対応はA28–A39と継続補強項、後続のactual cut/tower/公刊入力は別の責務である。最終P14の完成証明書ではない。
