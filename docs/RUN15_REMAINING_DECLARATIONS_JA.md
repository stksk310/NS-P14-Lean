# Run15 — 元の8目標の閉鎖と後続境界

**数学的未完：Run15の範囲では0。** 最終検証・レビュー・Pushの状態は
`RUN15_CLOSURE_STATUS.json`、`verification/run15_closure/verification.json`、gitで確認する。

元の未完命題を定義した `audit/run15/RemainingGoals.lean` は凍結して保持する。
そこに新しい公理や証明fieldを追加せず、
`audit/run15_closure/ClosedGoals.lean` の `Run15Closed.all_original_goals_closed` が
**元の8命題そのものの連言**を証明する。productionは監査moduleに依存しない。

| 命題 | 現在 |
|---|---|
| APBettiGoal | 証明済み：一般d≥1、任意元体、actual代数的半群環、全正行 |
| APConeBettiGoal | 証明済み：actual半群環と接錐、各自の最小表示、全行 |
| HarmonicGoal | 証明済み：実加群基底・実±1 minor・有理数による計数 |
| RelativeTerminalGoal | 証明済み：actual Rの末端r+1、Gのk有限性は仮定しない |
| ActualTorToRowGoal | 証明済み：同一cut、同一tower、同一Hから既存rowへ |
| CorrectedFullTransferGoal | 証明済み：実H0のZ作用、定数補正、intrinsic全e変数 |
| OrdinaryBettiBoundGoal | 証明済み：e≥3、任意元体、全正行。容量上界自体は幅仮定不要 |
| OrdinaryActualCompletionGoal | 証明済み：e≥3、w≥m−1、literal完成source/target、0を含む全行 |

一般APのD端点、1..v剰余規約、範囲外0、Fmin下界と幅単調性、実幅、
literal狭幅targetの公式も `ProfileBounds/Width/IntervalAPBetti` で証明した。
証明先と原稿への変更は `RUN15_CLOSURE_LEDGER_JA.md` を参照。

過去のPARTIAL台帳・検証・ZIPは各時点の事実として保持する。
過去の「未完」は現在の未完一覧ではない。未完命題を消して完成としたのではなく、
元の型を変えずに証明を与えた。

後続の未実装範囲は狭幅source比較の端点core/移行、Kneser/SC、BHP/EK、
N4/LTV、小生成元、全域合成であり、Run16–20の担当。
**P14全域のLean化完了はまだ宣言しない。**
