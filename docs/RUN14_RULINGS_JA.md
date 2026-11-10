# Run14 実行判断台帳

1. Ruling: 指定された既存work checkoutと通常Pushを継続 — Run13の全sourceと固定依存をhash/内容で照合し、実行済み接続を維持する — 未完のRun14をRun13再実装として報告しない。
2. Ruling: least offsetはまず正のactual半群元の表示で最小化し、shortest表示が全て非x atomであることを後で証明 — 表示長・orderの既存APIを使える — この後段を省くと原稿のoffset語との同定が欠けるため`shortest_offset_factors`と`leastOffsetWord_exists`を保持。
3. Ruling: 安定化から先に実terminal添字の有限性を閉じる — A/N/Tのfinrankを無限次元に対して使わない — 粗いstabilizationBoundを鋭い体積予算に流用しない。
4. Ruling: 最大Q₂→Sidonを体に依存しないSym2 countingで証明 — quadratic basis数の最大性から全二次単項式の非零性・一意性を同時に得る — 0・平方・異次数の衝突を別に排除し、標数2と偶数mをテスト。
5. Ruling: r=max(2,p)の三角下界とmaximal-cut系はr≥3に限定 — Γ=<6,7,11>のactual反例がある — r=2からSidonを得る過大適用を禁止。
6. Ruling: F_sをAのactual homogeneous idealへ束ね、U_sの低次数商写像を先に閉じる — 第三同型だけではtruncated towerや生成次数は得られない — 後者は未完と明記。
7. Ruling: Hは実U_sのdegree次元から一度だけ定義し、actualLayersもこのHで固定 — 同じ資源列の契約を早期に確定 — head/budgetを未証明fieldとしてDataへ注入しない。
8. Ruling: Greenが未完のままcut存在・資源上界・actual Data完成とは言わない — 指令の明示的禁止条件 — 未完の型を`audit/run14/RemainingGoals.lean`のProp定義と保存文書で示す。
9. Ruling: 不要なMathlib.Tactic一括importを外し必要なOmega/Monotoneだけへ絞る — 依存の大量再buildと二つの自分のbuildの競合が発生したため原因を調査 — 自分が起動した二つのbuildだけを停止し、その後単一buildで検証。他の旧processは変更しない。
10. Ruling: Run13のproof-erasure対応の公理監査を引き継ぐ — raw axiomInfo stubを真正な新公理と誤認しない — collectAxioms、自己依存、ソースの禁止構文を全て検査し原種別も保存。
11. Ruling: Run14完成前にRun15へ進めない — 20run目標で完成条件を弱めない — 完成run数は13、Run14は継続待ちとして再校正。
12. Final Ruling: fresh reviewerのroot audit coverage指摘を反映 — 現rootはimportのみだが将来の宣言も監査する契約を維持 — `NSP14.lean`のsource scanと正確なmodule名`NSP14`を追加し、45コマンドを再検証してから公開。
