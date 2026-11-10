# Run14：継続後の閉鎖exportと次runの境界

基準：途中版 `8040c90138bf1aa76cc99d9a5e7df7b2c1a8a206`。
Run13完了基準 `d8556dc`、詳細指令は既存Run14 plan。
最新の機械判定は `RUN14_CLOSURE_STATUS.json` と `verification/run14_continuation/verification.json`。
旧PARTIALの説明は8040c90と旧ZIPに保持し、その検証原本は変更していない。

| 指令の接続 | 現在のexport | 正確な範囲 |
|---|---|---|
| actual sourceと一つのcut | `Ordinary.ActualWitness`, `canonicalActualWitness` | S、e≥3、固定した同標数無限拡大上のcut。数値は全てSから導く |
| 鋭い体積 | `offsetLevel_path_bound`, `offset_volume_bound` | least-offset rank順列によるmin boundとδV。m=1・δ=0を含む |
| Green | `exists_quadratic_rank_bound`, `exists_hyperplane_flag`, `actual_green_flag` | 実minor多項式と双線型積による任意標数の次数2証明。全prefix同時 |
| cut存在 | `linearCutData_nonempty`, `infiniteFieldCut` | r=max(2,p)の独立形式、同cutの二次span全体・高次消滅。有限体はk(X)上 |
| S₀→P | `toPolynomialRing`, `polynomialForms_independent`, `restrictFunctor` | S₀の独立な一次形式の持ち上げ。Pは形式的r変数環。A像の独立性は仮定しない |
| actual短完全列 | `tower_exact`, `towerStratumEquiv`, `cutTower_exact`, `towerX_top_zero` | 実K=F_s/F_(s−1)とM_s→X_(s+1)。S₀から同じPへの制限。K⊂Mは実head次数を使う |
| 次数と生成元 | `sameJumpCutIso_degree`, `cutTower_generated`, `cutGeneratorQuotientEquiv` | 継承次数差s、X/Mの単一次数生成、実augmentation商と底次数の同型・極小生成元数 |
| actual区間 | `towerResource_card`, `headContributes_apery`, `headContributes_nonapery` | actual U_s基底に一致する二種の区間。Hは先行版と同一定義 |
| 全tail資源 | `contributing_residue_injective`, `towerResource_le_multiplicity`, `actualLayers_mass_offset`, `actualLayers_budget` | 全次数cap、総mass恒等式、δV。scalar cutoffによるtail切捨てなし |
| head資源 | `towerResource_head_identity`, `terminalLinearCount_le`, `towerResource_head_linear` | H1+a=δ+ell、ell≤e−1、同cutからH1≤rδ。r≥3のみ三角数cap |
| 体の整合性 | `towerResource_field_independent`, Run13 actual Betti extension | Hは実ラベルcardに一致。cutの存在は原有限体へ戻さず、Betti比較を戻す準備を保持 |
| actual Data/数値全行 | `actualNumericalDataWithCut`, `ActualWitness.numericalData`, `actual_all_rows`, `ActualWitness.all_rows` | 同じ実H・同じcutの全条件と既存actual Sidon境界から全行比較 |

## 歴史的な未完Propを閉じる検査

`audit/run14/RemainingGoals.lean`は原文のまま凍結。
`audit/run14_continuation/ClosedGoals.lean`はその同じ5つの型に対する証明を与える。
`ResourceBoundsGoal`はe<3も、head恒等式とell≤e−1およびδ=0分岐から閉じる。
cutとactual Dataの構成範囲は元の指令どおりe≥3。
production証明はこの監査ファイルや未完Propを入力として使用しない。

## Run15へ残す正確な範囲

Run14指定のGreen・単一cut・offset・actual tower・資源・Sidon・数値全行比較について、
未証明の数学入力をconstructorに追加していない。
P14全体やordinaryのactual Betti評価の完成をここから推論しない。

1. 同じP・同じtowerを使うactual Koszul/Tor rank評価（O_HARMONIC/O_TOR）。
2. 算術列targetの公刊入力の形式化と、target Bettiの同定。
3. actual Tor評価からRun14の数値行比較へ通すordinary閉鎖。

公刊入力に必要な独立査読と最終P14定理の接続も、今回のRun14検証とは区別する。
