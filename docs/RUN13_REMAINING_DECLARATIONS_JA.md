# Run13 接続境界と後続入力

基準Run12：`6b8d16889ea9b4d88567f0d9ac70391db2a49824`。
途中版`92cbe8f`の未完リストはgit履歴・`verification/block13/`・PARTIAL ZIPに凍結している。
この文書はその継続後のexport対応表。形式検証と独立レビューの最終判定は
`RUN13_CLOSURE_STATUS.json` と `verification/block13_continuation/verification.json` を参照する。

| 旧未完境界 | 今回の証明済みexport | 前提の供給・意味 |
|---|---|---|
| Tor比較の自然性 | `torKoszulIso_naturality`, `ordinaryTorKoszulNatIso` | 実tensor写像・実解消comparisonから証明。通常Torは第二因子kを解消する規約 |
| 極小自由解消rank | `MinimalFreeTower.toProjectiveResolution`, `minimalResolutionBetti` | 実自由基底、実syzygy短完全列、inc.image⊂変数部分加群という極小性から証明。比較等式を入力にしない。極小解消の存在は使用しない |
| graded複体・有限台 | `koszul_d_homogeneous`, `gradedKoszulComplex`, `gradedKoszulHomologySumIso`, `gradedBetti_total`, `gradedBetti_eq_zero_of_gt` | 内部次数=係数次数+i。実dを部分空間へ制限し、d²は元の実d²から得る。無限直和のexactnessと有限total Hから有限台を得る |
| 通常Torのgraded分解 | `ordinaryTorGradedSumIso` | 通常derived Torが実graded homologyの直和と同型。Torの名前の付替えではない |
| actual grading | `fullGGrading`, `nonXGGrading`, `actualTGrading`, `actualAGrading`, `actualNGrading`, `actualQGrading`, `descendingStratumGrading`, `ascendingStratumGrading` | 既存のorder次数部分加群・既存の指数座標を用いたwitness |
| 同jump次数差 | `jumpStratumGradedKoszulIso`, `jumpStratum_gradedBetti` | Run12の同じ`jumpStratumEquiv`、内部次数t→t+s。全体T≅Nは主張しない |
| 完備接錐 | `completedTorIso`, `completed_totalBetti`, `completedGradedKoszulIso`, `completed_gradedBetti` | 同じ全e変数の比較。完備側gradingはRun12のideal-power graded比較を運ぶ |
| 加群完全列→実Koszul/Tor LES | `koszul_shortExact`, `koszulConnecting`, `tor_exact_middle`, `tor_exact_connecting_left/right` | 実cone成分写像を用い次数ごとの短完全性を証明。H₀も含む |
| Betti補正rank | `koszulCorrectionRank`, `koszul_betti_rank_correction`, `koszul_betti_rank_correction_zero` | finite Pからfinite k-homologyを供給。δᵢ・δᵢ₊₁を保持し、差を自然数の切捨てで隠さない |
| rank Euler・有界比較 | `partialEuler_syzygy`, `partialEuler_nonnegative`, `partialEuler_terminal`, `boundedFilteredComparison` | 実exact有限ベクトル複体、実monic filtrationとcokernel商を入力にする。任意Betti配列やspectral degenerationを入力にしない |
| 実L[X]加群 | `polynomialBaseChangeModule`, `polynomialBaseChange_finite`, `koszulPolynomialBaseChangeIso`, `totalBetti_baseChange` | L⊗ₖMの実作用を構成し変数作用をpure tensor上で確認。Mがk有限とは仮定しない |
| 体拡大の自然性 | `polynomialBaseChangeCoefficientNatIso`, `koszulPolynomialBaseChangeIso_naturality`, `polynomialKoszulHomologyBaseChangeNatIso`, `homologyBaseChangeNatIso` | 非斉次加群写像を含む実chain mapについて自然。flat homology比較も自然同型 |
| 拡大gradingの体拡大 | `extendedGradedKoszulInclusion`, `extendedGradedHomologySumIso`, `gradedBetti_baseChange` | 拡大gradingの次数t複体はL⊗ₖKₜ。実L[X]Koszulへの明示的inclusionを持ち、そのHがactual changed Koszul Hを直和分解する。通常の拡大gradingを採用している |
| actual L側のgraded同定 | `gradedScalarKoszulIso_commutes`, `actualG/T/A/N/Q_gradedKoszulBaseChangeIso`, `actualG/T/A/N/Q_gradedBetti_baseChange` | 既存actual係数変更mapとinclusionの可換性を保って、独立したL側order-gradingへ同定。実pieceの指数fibreとpure tensor座標から供給し、target gradingをtransportで置換しない |
| actual係数変更 | `fullG_baseChangeIso`, `actualT/A/N/Q_baseChangeIso`, `actualG/T/A/N/Q_totalBetti_baseChange` | 実変数行列を既存指数基底で比較。G行列はlive-order条件つき0/1、T/商の行列は実restriction/projection。形式級数環全体のtensor同型を使わない |
| 初項・block rank | `standardMonomialBasis`, `triangular_signed_minor_rank_lower_bound`, `signed_integer_minor_rank_lower_bound` | 全ideal初項によるactual商の基底、実三角minorと±1対角から任意標数のrank下限 |
| 数値例 | `residue_totalBetti`, `principal_totalBetti`, `Run13ClosureFixtures.square_betti` | 残余体βᵢ=binomial(n,i)、P/(X²)=(1,1,0,…)、標数2を含む |

## 後続runが供給するactual入力

これらはRun13の未証明比較定理を仮定する境界ではない。後続のP14対象を上の証明済み一般定理に入れる責務である。

- Run14：選んだ実cut変数、正則性、有限cut商、必要なら有限体から同標数の無限拡大を選ぶ。source全e変数と非xのe−1変数S₀とcutのr変数を区別する。
- Run15/16：ordinary/AP targetの実表示、harmonic/initial idealの全競合、実tower短完全列、connecting mapの特定rank、rank Eulerへ入れる実exact有限ベクトル複体（例えば証明したflat性による局所化）とrank 0の供給。
- Run17以降：共通端点でのactual移行、公刊7入力、N4・小ordinaryの算術不等式、最終P14。これらは今回証明したとは扱わない。
- 一般の`Tor`と`Tor'`の全対象balancing定理は追加していない。P14で必要な実極小自由解消のrank橋はsyzygy LESで証明しているため、この未使用の汎用定理を入力にもしていない。

## Universe interface

Tor/monoidal接続は`k σ : Type u`、`ModuleCat.{u}`。actual半群の便利exportは`k : Type`。
任意標数性を制限する仮定ではない。高いuniverseでのactual変数ULift/renameは現在のP14 exportには使わない。
