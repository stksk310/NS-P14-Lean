# Run16 ledger — plan: docs/superpowers/plans/2026-11-10-run16-endpoint-kernel-transfer-order.md

基準: 447b7ae782414b739968a2a3009dd3a52ae230d0 (origin/work一致、clean)。
指令: 0cda4e8597ea1bafa8770b851ff2373973ee0e03。2026-11-11 JST開始。
Run15の8目標はClosedGoalsの元の型で証明済み。COMPLETE表示を証明入力には使わない。

Ruling: このmanaged workspaceの既存workブランチを継続する — ユーザー指定のwork更新と全過去の同じ固定環境を保つ — 別の並行writerが現れた場合はfetchして保持/統合する。
Ruling: cloud skillの実行スクリプトはローカルfilesystemの実行可能ファイルとして提供されていないため、同じ台帳/受入/一回の最終reviewをリポジトリ内で管理する — 実際の証明とレビューを省かない — 台帳の更新漏れがあればcompaction後の復旧コストが増す。

## Pre-flight interfaces

| producer → consumer | actual contract | status |
|---|---|---|
| T1 → T2/T3 | 広いEH、同じactual source、真正なq+2原子 | Finset offsetから構成予定。du<mは要求しない |
| T2 → T3/T4 | 実core、全射、有限E加群座標、全Min M | ideal座標を実作用へ接続する |
| T3 → T4 | N=M∩T、全j停止、E有限生成、rank0 | T単独を核と呼ばない |
| T4 → T5 | 端点homology=(PG,PG+R,R)、同じ内部作用 | Gはk有限としない |
| T2/T4 → T6 | QC Artin、実一次独立、PC/W/Hx/Rhat | 一般qでQCは非単項式を許す |
| T5/T6 → final | 同じGのintrinsic full Tor、任意体・全行 | i=0の負添字をguardする |
| Run15 → T5 | correctedActionComparison、有限homologyのみ | 実際の型を確認済み、同じnative作用へ適用する |
| Run12/13 → final | completedGradedAlgEquiv、nativeFullAtom_betti、通常Tor | 実際の型を確認済み、S変数順序を同定する |

## Scope / progress

11 ID: I_NORMALIZE, E_CORE, E_COORD, E_KERNEL, E_STOP, E_BOUNDS,
E_HOMOLOGY, E_TRANSFER, E_ARTIN, E_ROW, E_TWO。すべて未完から開始。

- Task1–6: 数学的なactual接続を実装済み。最終判定はclosure statusと最終検証記録。
- Task7: 全回帰・独立レビュー・監査ZIP・通常Pushを実行中。

小補題/ファイル/内部commitをrun終了にしない。証明・回帰・原稿台帳・監査引継ぎ・Pushまで継続。

## 時系列履歴（以下のpendingは当時の状態）

Task1: raw EH Data/source/atoms/multiplicity/embeddingDimension/width GREEN。
RED: verification/run16/red/EndpointData.log (Endpoint.Data未定義)。
GREEN: lake build NSP14、lake env lean tests/EndpointData.lean → exit0。
具体例は(6,1,[1,3],4)と(7,2,[1,3],4)。後者はdu=8≥m=7を保持。
一般gcdによるcofinite性はmathlib Nat.exists_mem_closure_of_geへ実際に接続した。
同じmを保持し、全offset最小性はactual closure上の分解長とgcd(m,d)で証明。
Task1全体は狭幅正規化と全変数表示の接続が残るため未完。

Task1主要接続: WidthNormalization/Endpoint.Normalization/OffsetOrder/Presentation/CarrierTransport。
元のSの非零offset gcdと各正規化offsetを実最小原子から構成し、同じcarrierと同じmを証明。
同じcarrierの選んだconductorはactual order/graded pieces/実接錐/通常Bettiを変えないことを実証明。
3環の変数数は(q+2,2,q)、全環とactual最小表示はrename AlgEquiv、通常Betti保存へ接続。
Task2 in progress: 二変数degree/offset AddSubmonoidと実monoid algebra coreを構成中。
Kernel/Tor/資源の結論をData fieldに追加していない。

Task2: corePointsの実加法monoid、Core=AddMonoidAlgebra、coreToG環写像、surjective、
全最小表示からの可換図がGREEN。E_COREの残りとして線型kernel=死んだcore単項式のspanを実装中。
Task1の4受入(Data/Normalization/Presentation/CarrierTransport)はexit0。

Candidate (未証明): E_HOMOLOGYのEulerをHilbert syzygy/局所化の代わりに、
x-Koszulの有限homologyとv倍の実mapping cone LESで閉じる。
v^m=0とE有限生成ならH_0(x;G),H_1(x;G)はk有限。
そのself-map vのconeのH三項から直接H1=H0+H2を得る。
Gのk有限性は要求しない。候補段階なのでE_HOMOLOGYを完了に数えない。

Task1 complete (I_NORMALIZE): actual narrow normalization, broad raw EH, actual minimal full presentation, original-source graded/completed/Bettis transport. Six scoped acceptance files including core/coordinates have exited0; root build5668 jobs PASS.
E_CORE complete: actual coreToG AlgHom surjective; coreToG_kernel_span exactly the killed core monomial span; full presentation diagram proved.
E_COORD remains partial: only coordinate index equivalence, no E-module direct-sum/finiteness/short words/antichain bounds yet. Continuing same run.

E_COORD major connections GREEN: genuine E-module C≃directSum M; Min words pure internal with length<u; all fibers nonzero; Hx<=u-2; actual finite ideal generating set proved. E_KERNEL actual G≃directSum M/N is E-linear, N independently actual dead-order ideal, N=M∩T. E_STOP exact all-j finite stopping, E-finiteness, v^m=0 and rank0 GREEN. Endpoint homology finite over k and ordinary E-Tor comparison GREEN; no k-finite G input. Remaining actual quotient/PC/W/R bounds/homology Euler/transfer/Artin/final rows pending.

Geometry/transfer regression: root5758 jobs PASS; 26 scoped acceptance files PASS in verification/run16/transfer/results.json. FullTransfer combined bound, original completed/narrow transports, actual zero/top/above rows built. QC Min basis and PC<=W, genuine internal polynomial presentation/grading and degree-one labels independently built. This is an internal durability checkpoint; same Run16 continues; Rhat/general Artin/q2/final audit unresolved.

E_HOMOLOGY closed: TwoActionTop actual chain top, cycle/joint kernel and actual H2 native G-linear equivalence; Socle actual simultaneous x/v annihilator, finite k, actualR=its finrank. CoreHilbert h0=1, h1=q and n>=u vanishing GREEN. Rhat injection/count remains E_BOUNDS, not hidden in E_HOMOLOGY claim.


Ruling: E_ARTINの三つの第一行評価の導出には、計画記載のparent/child重み計数を新規に重複実装する代わりに、Run15の`generated_harmonic_bound`（実初期加群・標準単項式・実Koszul rankに基づく一般定理）のj=1を使用する。真の斉次ideal Iについて実商の標準単項式座標・次数分解・有限台・h0=1・h1=q・次数0生成・b0=1を今回証明し、`artin_first_harmonic`、全三形、q=5の符号付き差を導出した。`artinFirstIdealIso`は実完全列0→I→T→T/I→0のconnecting mapからb1=dim(I/(y)I)を供給する。— 同じ結論を既存のより一般的な実証明で得て依存の重複を避ける判断。原稿ではIV.21の証明経路をこの調和型評価へ差し替える必要がある。— 誤りの場合の費用：計画のparent/child計数の独立形式化が別途必要となるが、一般商の全行exportに未証明のArtin評価を入力してはいない。

Tasks1–6: 数学的接続を実装し、11 IDの受入型を `audit/run16/ClosedGoals.lean` に固定。一般Artin商、実完全列によるb1/ideal Tor0、全三形、q5、±1 minor、元の狭幅完備接錐への全行APIまで接続済み。実R角基底・内部σ_C基底を別々に構成し、q2単項式性を別証明した。すべての新規production moduleのroot build（5894 jobs、後追加時は最新ログを正本）を警告なしで通過。

Concrete acceptance: `EndpointComputedExamples.lean` は三例のPC/PG/R九等式を任意体で証明。標数2にも実適用。大きすぎるR計算窓での最初の`decide`はheartbeat制限に達したため、実competitor上端を証明してから小さな窓に制限する `actualR_computed_window` を追加し、同じR値を核で検証した。heartbeat制限の増加・native_decide・検算値のaxiom化は行っていない。反射のHx差、q3非単項式関係の生存、u最小端/u|m/height0,1,2,3を試験した。

Task7: `scripts/verify_run16.py --fresh-test-cache` を開始。過去baselineをbytes固定し、空のproject test cacheから依存順の全回帰と全新規宣言の型/公理監査を実行する。数値独立モデル799例は約1.1秒で通過。最終レビュー・監査ZIP・Pushが終わるまでRun16を終了扱いにしない。

Verification metadata repair: 最初のcold検証は146受入、既存数値、独立座標モデル、公理抽出がexit0。その後、28 test moduleにexport宣言がないためcoverage assertionが停止した。原因は匿名exampleの非永続性であり、production宣言の欠落ではない。同じ受入命題61件を32ファイルで名前付き定理へ変更し、全test moduleも型監査する既存assertionを緩めず再実行した。旧試行はfinal_attempt_anonymousに保存。source/evidence hashと全cold回帰を新しい名前付き版に対して作り直す。

Named acceptance scope repair: 第二試行は0..137番まで通過。EndpointStandardArtinの三つの名前付き受入定理で、証明本体だけが参照するsection仮定hp/hh/h1/hqに明示includeが必要だった。意図した同じ仮定を宣言へ明記し、該当ファイルと後続六ファイルを個別に再検証して警告/エラーなし。その後、最終source hashを一つのcold結果に束縛するため全回帰を再実行。旧試行はfinal_attempt_named_scopeに保持。production証明は変更していない。

Task7 cold verification: FINAL PASS_RUN16_PROOF_CLOSURE。150 commands、146受入、7835環境宣言、1629新規宣言（通常/explicit型）、2160過去原本をbytes固定、production7586行。総コマンド実測440.594秒。全件exit0/警告なし。許容依存はpropext/Classical.choice/Quot.soundのみ。source集合・hashの前後一致、自己依存なし。これを固定commitに保存し、一回のfresh-context全体レビューへ渡す。

Final review: fresh-context gpt-6-astra /root/run16_final_review、base447b7ae..f010c72。116production/47acceptanceを全件passごとに検査。664source/155evidence/2160凍結hash、公理7835宣言、独立Lean再実行7件を確認。Ready、Critical/Important/Minor=0。再判定でも修正・延期Minorなし。追加の数学的fix passは不要。

Final: Ruling: Run17–20の数学と最終P14合成は今回のレビュー対象外 — 指令の担当11IDを閉じ、後続担当を維持する — 誤るとP14全域までLean完成したとの過大表示になるため、その完了は主張しない。
Final: Ruling: 任意非斉次idealの大域的最小生成集合アルゴリズムは対象外 — μは実idealのTor0/Nakayama fibreの次元という標準次数付きの定義で、実connecting同型を証明している — 誤ると利用者が未供給の生成集合構成を期待するため、原稿台帳で定義の範囲を明記する。
Final: Ruling: 完成原稿の改訂・公刊は対象外 — ユーザーはLeanと原稿を最終一致させる記録を求めており、現段階は対応台帳を供給する — 後で原稿へ反映する作業が残る。
Final: Ruling: 最終ZIP・Push・clean状態はproof commitの独立レビュー後に実行側が検証する — future actionをレビュー済みと偽らず、source/evidence hash・CRC・remote SHAを実測する — 検査を誤ると付属記録/公開状態に不一致が残るため、通常Push後もremote一致とcleanを確認する。

Publication validation: pending状態ではpackagerが期待どおり拒否しZIPを作らないことを確認。COMPLETE/独立レビューPASS後の正の実行で、source/evidence hashを再照合し、812ファイルのZIPを作成、CRCと全格納ファイルSHAを照合してexit0。archive自身のSHAは隣の.zip.sha256を正本とし、自己参照するledger内hashは作らない。公開commit後の通常Pushとremote/clean確認を継続する。
