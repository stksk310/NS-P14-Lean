# Run15 x比較・末端行の継続記録

基準は公開work `0604586a39f2b3579e995bbbc789df70cca07107`。Run15全体は引き続き未完であり、この記録は途中成果の監査用である。作業はここで終了しない。

今回の閉じた接続は、同じwitnessのactual x完全列 → 実Koszul写像錐 → r+1変数R上の通常Tor → 第1x比較と相対末端消滅である。P上のGの有限性やk上のGの有限次元性を仮定しない。共通部分は `TwoStepCone`、`CoefficientConeBetti`、`CoefficientFactorCone` にあり、actual exportは `RelativeXComparison.relative_Euler_le` と `RelativeTerminal.relative_Euler_terminal`。

元の `audit/run15/RemainingGoals.lean` は変更せず、`audit/run15_xclosure/ClosedGoals.lean` で同じ `RelativeTerminalGoal` を追加前提なしに証明した。既に閉じたHarmonicGoalと合わせて、この2つの元目標が証明済み。第1x比較の先にあるactual B評価と資源rowへの接続はまだ未完であり、ActualTorToRowGoalの完成とはしていない。

さらに実slotの完全性、定数射影を通る変数作用のrank上界、独立な変数像からの実±1 minorのrank下界を接続した。`SquareZeroEuler` は有限first-order加群の正確なEuler公式を与える。`SquareZeroModel` はk⊕k^(r+f)に実P作用を入れたモデルで、余分なf生成元とH0=f+1を保つ。このモデルとactual Bの同定は次の作業である。

検証は `verification/run15_xclosure/verification.json`。空のproject test cacheから77コマンドが通過し、35新規数学module・2,044行、新規441宣言を含む全4,636宣言を検査した。許容依存は propext、Classical.choice、Quot.sound のみ。過去の数学・試験・スクリプト・検証証拠1,186ファイルが基準commitから不変であることも検査した。検証コマンドの実測合計は234.1秒。actual Gamma=<6,7,11>の標数2のx比較とr+1末端、余分な生成元を持つfirst-order加群の非零boundary、第0行・第1行・topを含む。

再現は、この基準commitを含むリポジトリのcheckoutに本スナップショットを重ね、固定Lean/mathlib環境で `python3 scripts/verify_run15_xclosure.py --fresh-test-cache` を実行する。ZIP単独でgit履歴やmathlibを代替するものではない。新規宣言の通常型・explicit型と全公理依存は同ディレクトリの `declarations.json.gz` に収録。

原稿への対応は台帳A57/A58。第1x比較は実connecting rankを保持した二つの写像錐による代替証明であり、未証明の退化仮定を置いていない。一般AP Betti・ring/cone Betti一致・actual B・H0作用を保持する全変数移行・ordinary全行閉鎖は未完のまま引き続き構築する。
