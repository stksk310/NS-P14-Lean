# Run15の実測と20run目標の再校正

Run15は未完。番号を進めるためにordinary閉鎖の完成条件を弱めない。
数学sourceは23新規module、1706行。実際の通常Torを使うEuler/層接続とAP/targetの実対象を構成した。
検証の実測値はverification/run15/verification.jsonのchecks.seconds、core_line_count、宣言数を参照。
これは検証時間であり、思考・原典読解・Lean修正を含む全作業時間と混同しない。

## Run15を閉じるための残る数学的接続単位

1. **一般APのBetti**：実最小表示からGSSの解消exactness・minimality・rank又は等価なKoszul計算を構成し、半群環/cone一致・D端点・Fmin・actual intervalへ運ぶ。orderとx正則性は今回のexportを利用する。
2. **初期加群とharmonic**：実P^qのkernelに対するmodule版標準単項式、実Koszulの初項rank比較、±1 minorと有理平均。finite EulerとX/Mの単一次数生成は既存exportを利用する。
3. **相対/全表示/ordinary閉鎖**：x-Koszul第1鎖、Bの実同定、Rのc_(r+1)=0、同じZ作用のH0、補正付き有界比較、線型変数変更のTor保存。既存数値all_rows・今回の正確な畳み込み・Run13のactual体拡大と完成比較を接続する。

三つは既存数値不等式の代入だけでは閉じない。特に、最小解消の比較定理は任意対象の最小解消の存在定理ではなく、scalar標準単項式論は初期加群の実rank比較ではない。

運用上はこの三接続に追加3〜6回規模の長いrunを見込む暫定計画とし、全体20回の見込みを23〜26回へ再校正する。
これは新しい硬い上限ではない。数学的接続が閉じるまでRun15 COMPLETEを付けず、後続Run16–20の狭幅・Kneser/SC・BHP/EK・N4/LTV・全域合成の完成条件も保持する。
この幅は実装量と未構成の三つの証明機構に基づく作業配分の見積りであり、証明完了の保証ではない。
