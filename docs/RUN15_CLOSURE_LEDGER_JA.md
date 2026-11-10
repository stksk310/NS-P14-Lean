# Run15 最終接続台帳

数学の到達点は、元の8目標すべての無条件な証明。最終検証・レビュー・公開の状態は
`RUN15_CLOSURE_STATUS.json` と `verification/run15_closure/verification.json` で判定する。
指令は commit `586019b1c3063ac7160b1fc83a7da66ebbcf7311` の全文。
数学開始点 `fbfa5de`、Run14再現性修正統合点 `20aadbf`、最終差分の凍結基準は
`33079c170d038eddb432584837035566ae3577ae`。過去の部分検証・ZIPは上書きしない。

## 8目標の証明先

`audit/run15_closure/ClosedGoals.lean` の `Run15Closed.all_original_goals_closed` は、
凍結した元の8個の命題そのものの連言を証明する。productionは監査用命題をimportしない。

| 元の目標 | 証明先 |
|---|---|
| APBettiGoal | `Run15Closed.ap_betti_closed` → `Data.semigroup_totalBetti_pos` |
| APConeBettiGoal | `Run15APCone.ap_cone_betti_closed` |
| HarmonicGoal | `Run15Continuation.harmonic_closed` |
| RelativeTerminalGoal | `Run15XClosure.relative_terminal_closed` |
| ActualTorToRowGoal | `Run15BClosure.actual_tor_to_row_closed` |
| CorrectedFullTransferGoal | `Run15FullTransfer.corrected_full_transfer_closed` |
| OrdinaryBettiBoundGoal | `Run15FullTransfer.ordinary_betti_bound_closed` |
| OrdinaryActualCompletionGoal | `Run15Ordinary.ordinary_actual_completion_closed` |

## 最後のAP接続と原稿への変更

真正APのデータは m≥2、d≥1、1≤v<m、gcd(m,d)=1。最小原子は v+1 個。
v≥2 で補助ordinary半群 Γ=〈v,…,2v−1〉の実接錐 B から実AP head A への
全射を作り、その実核 J を用いる。核は添字 m 以上の実単項式基底で生成される。
x が J で正則であることから、J/xJ の実多項式作用を保持して通常Torを還元する。
有限商は下段 D=v−((m−1) mod v)、上段 v−D の二段加群であり、下段座標反転後の
Hankel作用をVandermondeの実可逆変数変更で評価作用へ移す。
既証明の実Koszul rank公式により、この有限商の全Betti行を得る。

最後の短完全列 0→J→B→A→0 のTor写像消滅には、新しい簡単な証明を採用した。
m>v より J⊂xB。x の単射性から x で割る実 B 線型写像 J→B を作る。
従って包含 J→B は、この写像と最後の多項式変数の掛け算の合成である。
Koszul複体上の変数倍の実null-homotopyにより、包含の全homology写像は0。
実LESから β_(i+1)(A)=β_(i+1)(B)+β_i(J) を得る。
無限k次元の J/B/鎖群にfinrank加法を適用せず、有限生成から得られる
**homologyの有限性だけ**を用いる。

これは過去の作業ノートにある「gradingから写像消滅を示す」候補の置換である。
gradingによるTor集中やGSSの解消そのもののexactnessを証明したとは主張しない。
GSSのquotient Betti公式と同じ結論を、actual Koszul計算で独立に証明した。
Herzog–Stamate型の半群環/接錐Betti一致は、既証明の実正則元商比較を用いる。
原典の型・添字確認は初期台帳に残すが、原典名を数学公理として使わない。

評価点は同標数の `InfiniteScalarField k` 上で選び、実接錐の全変数Bettiの
体拡大保存により元の任意体 k に戻す。有限体上のcutや評価点の存在は主張しない。
v=1 は既証明の実二生成元の場合を使う。d=1への縮小はない。

## 指令の残りの要求との対応

| 要求 | 実装と範囲 |
|---|---|
| P、R、全e変数 | 既存のrelative/full variable change、実Tor同値。Pはr、Rはr+1、fullはe変数 |
| harmonicと同cut tower | 実標準加群基底・±1 minor、実LES、同jump strata、同じHのresource row。継続台帳参照 |
| H0補正と末端 | native H0のZ作用を含む実同型、補正済みfull transfer、relative末端r+1、全Betti行 |
| 一般AP全行 | `BettiFormula.lean`：代数的半群環/実接錐/完成接錐の全行、0行は1 |
| m=av+b、1≤b≤v | `ProfileBounds.lean`：`multiplicity_blocks`、`blockResidue_pos/le`、`residueDefect_eq_blockResidue` |
| i>vは0、Fmin、単調性 | `positiveBettiProfile_above`、`semigroup_totalBetti_above`、`positiveBettiProfile_lower`、`apLowerProfile_monotone` |
| 実幅とliteral target | `Width.lean` の `maxAtom/width`、`IntervalCompletion.lean` の実carrier一致、`IntervalAPBetti.lean` のactual完成target公式・下界 |
| ordinary source全体 | `ordinary_betti_bound` はe≥3の全sourceにmultiplicity容量を証明。幅仮定が不要な強い結論 |
| ordinary literal completion | `ordinary_actual_completion_betti_le` はe≥3、w≥m−1、元の任意体、0を含む全行、各自の最小表示 |

狭幅の主比較、e=1/2の主比較、Kneser/SC、BHP/EK、N4/LTV、全域合成は後続範囲。
一般AP公式とliteral狭幅targetの計算を、それらのsource比較の証明済み扱いにしない。

## 最終受入と証拠

新規3受入ファイルは、一般AP d>1、v=1、D=1/v、i=D/D+1、0/top/top+1、
標数2、実Jの全行Tor写像0、実LES、狭幅literal完成targetを検査する。
凍結した既存受入で非零T・異jump・δ=0・r=2/3・relative top・H0補正等を保持する。
最終verifierは全fixture依存順・空project test cache・数値回帰・全宣言公理依存を検査し、
Run15全体の新規moduleについて通常型とexplicit型をまとめて保存する。
