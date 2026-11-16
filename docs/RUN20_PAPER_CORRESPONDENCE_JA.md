# Run20 / 最終原稿対応台帳

対象はV06 (全体 SHA fe8271bbaabf6b3d31243628c3a5a5a305b82361c794f03c6e13a2fe98c72791、第6章 SHA 67a10b00ab51ab1836fc071bb1c03b9fa2898ec470e84762151aeba032316f4d)。旧50 IDの原文・量化はJSONにそのまま保持し、実module・宣言群・actual consumerを対応させた。表は結論を公理化するものではなく、実証明の索引である。

## 全域合成

`NumericalSemigroup.p14_totalBetti_le_intervalCompletion S k i` は全S、元の任意Field k、全iについて、元sourceとliteral [m,maxAtom]閉包の完備接錐を各自の実最小原子変数で比較する。e1/e2/e3/ordinary/e4 narrow/e>=5 narrowの六領域は排他的。w=m-1はordinary、w=m-2はnarrow。r2に三角数条件を課さず、delta0の空塔を保持する。正規化dataは元のmとdを残し、物理幅V=duをuへ置換しない。

共通targetの同定ではNumericalSemigroup構造をconductor込みで同一視しない。同carrierから、双方自身の原子型と多項式環を運んだactual totalBettiを同定し、完備接錐比較へ二度のcompleted_totalBettiで移す。e1はliteral [1,1]。旧he>=2 APIは互換系として別に保持した。

sourceの上端とtargetの上端は異なる。<6,7,9,11>についてsourceのbeta5=0、target<6,...,11>のbeta5=5をAP公式で証明し、新しい公開入口も適用する。0行、source e/e+1、target自身のeは全称fixtureに含む。

## 保持する数学と十分な別証明

共通代数群および公刊入力 X_BASIC / X_LTV / X_GREEN / X_AP_BETTI / X_AP_CONE / X_BHP_EK / X_KNESER / X_SC のうち、X_BASICは共通代数群、残り七つが原稿の公刊入力である。引用名のaxiomは置かず、各module群の実証明とactual consumerまで追う。Greenは必要な次数2特殊版。LTVは同じ比較を一文字endpointから証明する十分な代替。SCはLevのconnected-rearrangement経由で元の単一unit/Nat総和の契約を証明。Kneserの採用ソース著作権/license/provenanceは既存のまま束へ含める。AP公式・AP接錐一致は全原子作用と元の体のTorに接続し、BHP/EKは同一Hilbert関数の実lex商と実初期rank、任意標数のdistraction/安定化を経由する。

一般Gはk有限次元とはしない。有限性は実homology/degree片/有限生成Tor/Artin商ごとに証明。ordinaryのPはr変数、相対Rはr+1変数、最小表示はe変数であり、一つのcut・一つのH_tとH0補正を維持する。元の体への下降はactualG_totalBetti_baseChange。端点は全jの競合核、元のR/Hx、PCとPGの実核長補償を保持する。

V06同期五項目は改変せず、N4は新cubic 4z^3+45z^2+140z+36、SC復帰、socle三角形、幅4の全m実核証明を採用する。旧83 profile/665比較/5tail、196証書、Navi増分は主依存にない。明示周期停止やexact antipodal presentation等は独立の旧成果として残し、Mainに不要な強さを形式化済みの必要入力として言い換えない。原典の追加LTV線形上界、任意初期idealの一般等式も主張しない。

## 50 ID 索引

原文/量化/列挙された全宣言/consumerは `RUN20_DEPENDENCY_COVERAGE.json`。必要な契約が閉じたことと、不要な原文の強さを区別したstatusである。

| ID | 対応種別 | production証明群 | V06 |
| --- | --- | --- | --- |
| X_BASIC | PROVED_NEEDED_GROUP | Homological.KoszulTor, Homological.KoszulAnnihilation, Homological.GradedBetti, Homological.KoszulLongExact, Homological.ComplexEuler, Homological.NativeKoszulExact, Homological.StandardMonomials, Homological.InitialModule, Homological.MinorRank, Homological.KoszulStandardMinor | BRIDGE / ordinary Tor / E-TOR |
| I_NORMALIZE | PROVED_NEEDED_CONTRACT | Semigroup.WidthNormalization, Semigroup.CarrierTransport, Endpoint.Normalization | BRIDGE |
| I_PARTITION | PROVED_NEEDED_CONTRACT | Main.Partition | §6.1–6.2 |
| I_BASE | SUFFICIENT_ACTUAL_PROOF | SmallEmbedding.Base, Semigroup.IntervalCompletionAll | §6.1 / BRIDGE |
| X_LTV | SUFFICIENT_ACTUAL_PROOF | SmallEmbedding.ThreePresentation, SmallEmbedding.LanTuVu, SmallEmbedding.ThreeComparison | §6.1 e=3 |
| I_THREE | PROVED_NEEDED_CONTRACT | SmallEmbedding.ThreeComparison | §6.1 e=3 |
| O_COORD | PROVED_NEEDED_CONTRACT | Semigroup.AperyDimensions, Semigroup.JumpFiltration, Semigroup.TerminalCoordinates, Semigroup.TowerCoordinates | ordinary coordinates / jump |
| X_GREEN | PROVED_NEEDED_SPECIALIZATION | Green.HyperplaneStep, Green.HyperplaneFlag, Green.QuadraticRank, Semigroup.ActualGreen | ordinary degree-two Green |
| I_FIELD | PROVED_NEEDED_CONTRACT | Homological.FieldExtension, Homological.ActualCoefficientBaseChange, Homological.InfiniteScalarField | BRIDGE arbitrary original field |
| O_CUT | PROVED_NEEDED_CONTRACT | Semigroup.SquareZeroCut, Semigroup.FixedTower, Semigroup.ActualResources | ordinary single cut |
| O_VOLUME | PROVED_NEEDED_CONTRACT | Semigroup.OffsetVolume, Semigroup.TerminalResidues, Ordinary.OffsetVolumeArithmetic | ordinary offset volume |
| O_TOWER | PROVED_NEEDED_CONTRACT | Semigroup.TowerExact, Semigroup.TowerResources, Semigroup.TowerIntervals, Semigroup.TowerStratum, Semigroup.FixedTower | ordinary same H_t |
| O_HARMONIC | PROVED_NEEDED_CONTRACT | Homological.Harmonic, Homological.StandardHarmonic | ordinary harmonic rank |
| O_TOR | PROVED_NEEDED_CONTRACT | Ordinary.ActualTorRow, Ordinary.TowerCombined, Ordinary.TowerH0, Ordinary.RelativeRowsAll, Ordinary.RelativeXComparison | ordinary Tor / H0 |
| X_AP_BETTI | PROVED_NEEDED_CONTRACT | ArithmeticSequence.BettiFormula, ArithmeticSequence.ModelTorClosure | CAP / AP formula |
| X_AP_CONE | PROVED_NEEDED_CONTRACT | ArithmeticSequence.ConeBetti, ArithmeticSequence.BettiFormula | BRIDGE / AP cone |
| I_TARGET | PROVED_NEEDED_CONTRACT | Target.IntervalAPBetti, Target.APLowerRows, Target.IntervalBetti, ArithmeticSequence.ProfileBounds, Main.IntervalTarget | CAP / MINCAP |
| O_TARGET | PROVED_NEEDED_CONTRACT | Ordinary.TargetMargin, Ordinary.IntrinsicFullTransfer, Ordinary.NativeFullTransfer | ordinary target transfer / H0 correction |
| O_LOW | PROVED_NEEDED_CONTRACT | Ordinary.LowRank | ordinary r=2,3 |
| O_SCALAR | PROVED_NEEDED_CONTRACT | Ordinary.Scalarization, Ordinary.HarmonicWeights | ordinary scalar all rows |
| O_SIDON | PROVED_NEEDED_CONTRACT | Semigroup.ActualSidon, Semigroup.ActualCutRank | ordinary actual Sidon |
| O_SMALL | PROVED_NEEDED_CONTRACT | Ordinary.SmallScalar | ordinary r=4..8 fixed cutoff |
| O_LARGE | PROVED_NEEDED_CONTRACT | Ordinary.LargeSeed, Ordinary.LargeScalar | ordinary r>=9 fixed cutoff |
| O_CLOSE | PROVED_NEEDED_CONTRACT | Ordinary.NumericalBettiClosure, Ordinary.Closure | §6 ordinary |
| E_CORE | PROVED_NEEDED_CONTRACT | Endpoint.Core, Endpoint.CoreMap, Endpoint.CoreKernel, Endpoint.CoreWords | E-CORE |
| E_COORD | PROVED_NEEDED_CONTRACT | Endpoint.Fibers, Endpoint.IdealCoordinates, Endpoint.FiberModule, Endpoint.Quotient | E-COORD |
| E_KERNEL | PROVED_NEEDED_CONTRACT | Endpoint.Competitors, Endpoint.Carry, Endpoint.ActualKernel, Endpoint.AssembledKernel | E-KERNEL / all j |
| E_STOP | HISTORICAL_PROVED_OUTSIDE_MAIN | Endpoint.Stopping, Endpoint.MinimalWords, Endpoint.MinimalBounds, Endpoint.Residues | historical E-STOP; absent main |
| E_BOUNDS | PROVED_NEEDED_CONTRACT | Endpoint.CompetitorBounds, Endpoint.SocleInjection, Endpoint.SocleBounds, Endpoint.FiniteSocleBounds | E-HEIGHT / E-BOUNDS |
| E_HOMOLOGY | PROVED_NEEDED_CONTRACT | Endpoint.HomologyFinite, Endpoint.HomologyBalance, Endpoint.ArtinQuotient, Endpoint.Socle | E-HOMOLOGY |
| E_TRANSFER | PROVED_NEEDED_CONTRACT | Endpoint.VariableOrder, Endpoint.NativeTransfer, Endpoint.Compensation, Endpoint.FullTransfer | E-TOR |
| W_EDGE | PROVED_NEEDED_CONTRACT | Width.EdgeAP, Width.EdgeHoleComparison, Width.EdgeHoleGeometry | W-EDGE |
| X_BHP_EK | PROVED_NEEDED_CONTRACT | Lex.BettiComparison, Lex.TotalBettiComparison, Lex.LexExistence, Lex.StrongStableEK | dense whole Hilbert lex / EK |
| W_DENSE | PROVED_NEEDED_CONTRACT | Width.DenseResources, Width.DenseLexResources, Width.DensePayment, Width.DenseComparison | W-DENSE t2 / t>=3 |
| X_KNESER | PROVED_NEEDED_CONTRACT | Additive.Kneser, Additive.KneserCore, Additive.ThreePointGrowth, Additive.FourPointGrowth | distance / growth |
| E_ARTIN | PROVED_NEEDED_CONTRACT | Endpoint.StandardArtinRows, Endpoint.ArtinRank, Endpoint.FirstHarmonic, Endpoint.ArtinWeights | E-ARTIN |
| E_ROW | PROVED_NEEDED_CONTRACT | Endpoint.FirstRow, Endpoint.PositiveRows, Endpoint.RowPackage | E-ROW |
| W_SPARSE | PROVED_NEEDED_CONTRACT | Width.SparseFirst, Width.SparseSecond, Width.HigherFromSecond, Width.SparseHigher, Width.SparseComparison | W-SPARSE |
| W_FIVE | PROVED_NEEDED_CONTRACT | Width.FiveSmall, Width.FiveHigher, Width.FiveNonAntipodal, Width.AntipodalComparison, Width.FiveComparison, Width.IntegerPayment | W-FIVE / APD |
| W_CLOSE | PROVED_NEEDED_CONTRACT | Width.Closure | §6 e>=5 narrow |
| E_TWO | PROVED_NEEDED_CONTRACT | Endpoint.TwoMonomial, Endpoint.TwoInternal, Endpoint.TwoRows | N4 / two internal variables |
| N_DISTANCE | PROVED_NEEDED_CONTRACT | NarrowFour.CoreWords, NarrowFour.SocleTriangle, NarrowFour.Distance | N2 |
| X_SC | PROVED_NEEDED_CONTRACT | Additive.SavchevChen, Additive.TwoValueSequence, Additive.StandardWordSequence | N3 SC return |
| N_WORDS | PROVED_NEEDED_CONTRACT | NarrowFour.StandardWords | N3 |
| N_HIGH | PROVED_NEEDED_CONTRACT | NarrowFour.CubicPayment, NarrowFour.HigherRows | N4a–c new cubic |
| N_FIRST | PROVED_V06_CONTRACT | NarrowFour.Relations, NarrowFour.FirstCount, NarrowFour.FirstLarge | N5 |
| N_SMALL | PROVED_NEEDED_CONTRACT | NarrowFour.SmallWidths | N6 |
| N_WIDTH4 | SUFFICIENT_ACTUAL_PROOF | NarrowFour.WidthFourCore, NarrowFour.WidthFourCompetitors, NarrowFour.WidthFourInitial, NarrowFour.WidthFourComparison | N7 all m / all j |
| N_CLOSE | PROVED_NEEDED_CONTRACT | NarrowFour.Comparison | N8 / §6 e4 narrow |
| I_MAIN | PROVED_NEEDED_CONTRACT | Main, Main.Branches, Main.IntervalTarget | §6.3 |

## 認証境界

このsource-bound台帳は数学的接続を記録する。fresh検証・全private宣言監査・独立レビュー・ZIP・実Pushの完了状態は後で作成する `verification/run20/` の別receiptに束縛する。旧失敗ログやPARTIAL台帳を遡及改変しない。
