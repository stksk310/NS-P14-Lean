# Run14継続後の20run再校正

Run13の完了基準はd8556dc、Run14途中版は8040c90。
継続でGreen・一つのcut・鋭いvolume・actual tower/生成元商・同一資源列・actual Data/all_rowsを接続した。
完成の機械判定と実測は`verification/run14_continuation/verification.json`を参照。
途中版の1,245行に加え、継続は38 coreファイル・3,112行。
最終検証は空のproject test cacheから50コマンドを通過し、検証時間合計168.52秒。
Lean/mathlibおよびproductionのbuild cacheは既存のものを利用した。
Greenだけでなく、既存の商・grading・scalar restrictionの実接続にも相当の実装量を要した。

20runは引き続き運用目標。Run14は途中公開と今回の継続を合わせて一つの数学的runと数え、
ファイル数・コミット数・経過時間で完成単位を割り増ししない。
一つのrunを30〜60分へ強制的に収める見積りは採用しない。

| 次run | 閉じる接続 | 校正後の見方 |
|---|---|---|
| 15 | 同じcut/towerからactual Tor評価、算術列target Betti、ordinary閉鎖 | Run14の数値・資源入力は使用可能。harmonic初項rankと公刊targetの実証明が残る大きな単位 |
| 16 | 狭幅正規化・actual端点core・核と移行 | 共通Koszul基盤は再利用可能。actual接続は別途必要 |
| 17 | Kneser / Savchev–Chenの必要形 | 公刊定理を未証明の入力として済ませない |
| 18 | BHP/Pardue・EKと五生成元以上の幅側 | 公刊入力と幅側actual化が重なるため配分の不確実性が高い |
| 19 | N4・幅4・小生成元 | 紙上簡約をactual証明へつなぐ。有限表の検算だけでは完了しない |
| 20 | 全域分割・actual主定理・原稿との最終一致 | 前runの未完を隠さず、全域・全行・任意体の証明を確認 |

残り6runでの到達は保証しない。Run15で公刊入力・初項rankの実装量を測り、必要なら配分を再校正する。
予定run数のために仮定や完成条件を弱めない。旧全体計画と途中版の履歴は保存する。
