# Run14：証明済みexportと未完の宣言

基準：Run13完了commit `d8556dc615b1e1633379f4567e9e795b3f1c8ae3`。
指令：`75e86da0ac24a02b1895f9ada84918c8e00e0fa9`の
`2026-11-10-run14-green-cut-tower-order.md`をfetchして原文を保存した。

**Run14は未完。** ビルド・公理依存検査は、実装したexportの証明を認証する。
Green・cut・資源・actual Dataまでの全指令の完成を認証しない。
Run13の不足を未証明入力にした部分はない。実装中にRun13の補修は不要だった。

## 閉じた接続

| 対象 | Lean export | 厳密な範囲 |
|---|---|---|
| least offset | `leastOffset`, `leastOffsetLength`, `offsetLevel`, `apery_eq_offset` | 実際の正の半群元の表示から構成。shortest表示が非x actual atomになることも証明 |
| 安定化 | `order_stabilization` | `lρ ≤ Lρ+q`なら実orderが`Lρ+q`。体に依存しない |
| 経路 | `leastOffset_prefix`, `leastOffset_prefix_injective`, `leastOffsetLength_lt_multiplicity` | 各prefixはleast、空prefixも含め剰余は相異なる、lρ<m。m=1を含む |
| 剰余別総jump | `terminal_residue_sum`, `mem_residueTerminalIndices` | 全terminalを含む有限添字集合でΣ(jump−1)=Lρ−sρ。任意に途中で打ち切らない |
| 有限性 | `terminal_finite`, `terminalFinite`, `nonAperyFinite`, `headAlgebraFinite` | 先に実基底添字の有限性を示す。A,N,Tのfinrankはこの後にのみ使う |
| Greenの整数パラメータ | `quadratic_decomposition`, `actualCutRank` | 整数分解とr=max(2,p)だけ。Green定理・cut存在の証明ではない |
| 体 | `InfiniteScalarField`, `infiniteScalarFieldInfinite`, `infiniteScalarField_charP` | 任意体kのk(X)は無限、標数を保持。既存actual Betti不変性に実際に適用 |
| F,U | `jumpIdeal`, `jumpIdeal_homogeneous`, `jumpIdeal_one`, `jumpIdeal_top` | Aの実イデアル。S₀上の既存filtrationと同じ支持 |
| 低次数 | `towerStageLowDegreeEquiv` | U_s=A/F_{s−1}のn≤sの実次数成分→Q_nが実商写像の同型 |
| H | `towerResource`, `towerResource_zero`, `towerResource_outside_support` | 実U_sの次数次元から一意に定義、H₀=δ、全次数の有限台。δ=0の空和も証明 |
| 数値層 | `actualLayers`, `actualLayers_mass` | head=H₁、tail_j=H_{j+2}、全tail有限台。massは全Hの有限和に一致 |
| Sidon | `maximalQDegreeAperyPairData`, `maximal_qDegree_multiplicity_bound`, `maximal_qDegree_deficit_bound` | maximal actual Q₂から実データ。平方、0を含む項、異次数衝突を排除。任意標数・任意m |
| 数値境界 | `actualNumericalBoundary` | r≥6かつe=r+1の既存Boundaryをactualに供給。途中のmaximal-cut系はr≥3でのみ成立 |

有限性用`stabilizationBound`は意図的に粗い上界で、δVの体積予算としては使っていない。
Aのcut像に代数的独立性を仮定した箇所はない。cut自体はまだ選んでいない。

## 正確な未完命題

`audit/run14/RemainingGoals.lean`は未証明の命題の**定義**だけを保存する。
`GreenDegreeTwoGoal`等の証明項は存在せず、productionのimportにも入れていない。
定義を型検査できることと、その命題を証明したことを混同しない。

1. `GreenDegreeTwoGoal S k`：無限体上、a=dim Q₂、p=quadraticIndex aに対し、
   S₀の独立なp本の一次形式を同時に選び、全s≤pについて
   dim(A/(先頭s本))₂≤choose(p+1−s,2)+max(a−choose(p+1,2)−s,0)を証明する。
   整数分解だけではこの存在命題を満たさない。
2. `OneCutGoal S k`：e≥3なら固定した同標数無限拡大k(X)上で、r本の独立な
   S₀一次形式を一度だけ選び、同じcutでAの次数≥2を消す。
   p<2の独立形式補完と、このPへの全加群作用・写像の制限も未実装。
3. `SharpOffsetVolumeGoal S`：Σρ≠0(Lρ−1)≤δ(e+δ/2−3/2)。
   lρ<mだけでは鋭い予算にならない。原稿(3.1)の
   Lρ_k−1≤min(δ,k−1)をactual atom剰余とprefixから証明する部分が残る。
4. `ResourceBoundsGoal S k`：既に構成した**同じH**で全tのH_t≤m−1、
   全mass≤δV、H₁≤rδ、r≥3でのhead capを同時に供給する。
   Apéry/terminal区間の剰余内非交差、区間和と実stage次数次元の一致、
   H₁+a=δ+ℓ（ℓは実degree-one terminal数）も未証明。
5. `ActualNumericalDataGoal S k`：e≥3で既存`NumericalClosure.Data`を作り、
   `D.layers = S.actualLayers k`を満たす。任意に都合のよい別の資源列を渡してはならない。

これらに加え、次のtower宣言はまだ型本体から実装が必要：

- `TowerX s := (U_s)_{≥s}`、`TowerM s := (U_s)_{≥s+1}`を継承されたgradingで構成。
- 実`K_s=F_s/F_{s−1}`からTowerMへの単射と、TowerM→TowerX(s+1)の全射。
- `2≤s≤ν`で`0→K_s→M_s→X_{s+1}→0`が同じP上の短完全列、`X_{ν+1}=0`。
- square-zero cutからX_s/M_sの次数s/s+1単独生成と、極小生成元数=実degree商次元。

このshort exactnessをU全体の第三同型定理だけで代用したり、k線型完全性だけを
P線型完全性と呼んだりしない。ここは今回完成と数えていない。

## Greenで未解決の中身

固定mathlibには必要な超平面制限のexportが見つからなかった。
一般二次積の対称双線型写像について、generic multiplicationのrankがR以下なら
その像全体の次元がchoose(R+1,2)以下となる形への還元を調べたが、
任意標数、とくに標数2の平方が消える場合を含むgeneric rankの形式証明は構成できていない。
この説明は証明候補であり、証明済み補題・公刊入力の代替とは扱わない。
無限体への拡大だけでgeneric cutの存在が証明されたことにはならない。

## 受入例

- Γ=<6,7,11>を実生成半群として同定。m=6,e=3,a=2,r=2。
  r=e−1でもa≠choose(e,2)、三角下界も不成立。
- Γ=<8,9,11>：m=8,e=3,a=3。偶数合成数でactual ApéryPairDataとSidon境界。
- Γ=<13,14,17,19>：m=13,e=4,a=6,r=3、δ=9、actual H₀=9。
- 既存のchanging-jump例：異なるjumpの二つのterminal、実A/N/Tの有限性。
- m=1、δ=0：最短語長0、資源列は空和で全て0。
- 標数2→k(X)：無限性・同標数性と、独立に構成したactual gradingのBetti保存。

各fixtureは表の数値だけを仮定せず、cofiniteな実加法半群、最小生成集合、Apéry集合、
order、次数成分をLeanで証明している。Pythonはfixtureの式を準備しただけで、真偽のoracleではない。

## 次に必要な接続

Run14の上記未完を閉じてからRun15へ進む。`Data.all_rows`自体は既存定理だが、
actual Dataがない現在、その条件付き数値比較をactual ordinary閉鎖とは報告しない。
actual Tor評価・target Bettiによるordinary閉鎖はユーザー指定どおりRun15の責務に留める。
