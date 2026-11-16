# Block11：actual N/Q・斉次性・Apéry基底・Hilbert関数

2026年11月10日（JST）。12ソース、81定理を含む120宣言。
Block01–10の証明ソース・テスト・固定依存は保持する。

## 実際の非Apéry部分N

AはBlock10の実環G/xG。head係数のうち非Apéry指数に支持を持つk部分加群から出発し、
Aのすべての元による乗算で閉じることを証明して `nonAperyIdeal` を構成した。
和がApéryなら両因子もApéry、という下方閉包を使う。
従って非Apéry項の積が生きていれば非Apéryのままで、死んだ積は0である。
単項式のこの性質を実際のhead基底で任意の係数の有限和へ延長する。

`nonAperyIdealEquiv` と `nonAperyIdealBasis_eq_initial` はN全体の基底をactual非Apéry headクラスへ同定する。
Aの各次数はGの実成分の像として定義し、内部直和分解と `GradedAlgebra` を登録した。
明示的係数フィルタが登録された次数射影と一致することを証明し、
`nonAperyIdeal_isHomogeneous` でmathlibの意味の斉次イデアルであることも保証する。

## Qはactual quotient A/N

Qを非Apéry headのidealによる環の商として定義する。
AからApéry係数を抽出する写像は全射で、核は正確にNである。
第一同型定理によりactual商からApéry上の有限支持座標への線型同値を構成する。

Q=A/N ≃ₖ (actual Apéry指数 →₀ k)。

`aperyQuotientBasis_eq_initial` が各基底ベクトルと実単項式の商クラスを同定する。
非Apéry指数のクラスは0、Apéry指数のクラスは非零。
積が非零である条件は「orderが加法的、かつ和がApéry」の両方である。
Qを単なる座標ベクトル空間として定義したものではなく、積は実商の積を保持している。

## actual quotientからの次数と計数

`qDegree n` はGₙ→G→A→Qの実写像の像である。
この像がorder=nのApéry支持空間と等しいことを証明し、その有限基底を構成した。
全次数はQ全体を張り、異なる次数は独立、積は次数和へ入る。
従ってQにも `GradedAlgebra` を登録した。

体kについて以下が成立する。標数の仮定はない。

- dimₖQ=m。
- dimₖQ₀=1、dimₖQ₁=e−1。
- dimₖQ₂≤δ=m−e。
- Σ₂≤n≤δ+1 dimₖQₙ=δ。それより高い次数は0なので、高次総量はこの有限和で表現する。
- Aₙ→Qₙはすべてのnで全射。n≤2では単射でもあり、自然な商写像そのものが線型同型となる。

非Apéry headは次数3以上なので、最後の同型に余分な条件を足していない。
原稿のA₂=Q₂はこの自然な同型として実装する。

## 標準生成・Artin性・最高次数

最長のApéry原子表示を一原子ずつ外すと、残りもApéryで積はliveとなる。
値についての帰納から、Qはactual非multiplicity原子の次数1クラスで生成される。
生成性を未証明のstructure fieldとして渡していない。
有限Apéry基底からdimₖQ=mを得て、mathlibの定理によりQをArtin環として登録した。

νを有限Apéry集合の最大orderとして構成する。
`qDegree_ne_bot_iff` によりQₙ≠0 ⇔ n≤ν、従ってこれがactual Qの最高次数である。
Block08の数値order上界をactual Qへ接続してν≤δ+1を得る。
この上界を得るためにQの標準生成を無断で仮定する必要はない。

## モジュール

| ソース | 役割 |
|---|---|
| HeadMonomials | actual Aの単項式・積・任意の有限和、Apéry下方閉包の接続 |
| NonAperyIdeal | A全体の乗算による安定性、actual ideal Nと係数同値・基底 |
| AperyQuotient | actual Q=A/N、射影の核と全射、Apéry基底 |
| AperyDegree | Gからの実次数像、次数座標、次数基底と積 |
| HeadDegree | Aの実次数像・射影、Nの成分ごとの安定性 |
| LowDegreeQuotient | 自然なAₙ→Qₙとn≤2の同型 |
| AperyDimensions | actual総次元・Hilbert関数・高次総量 |
| AperyProducts | N基底と実クラスの一致、Qでの非零積の正確な条件 |
| AperyStandard | 次数1のactual原子による生成、Artin環 |
| AperyGradedAlgebra | Qの内部直和とregistered grading |
| HeadGradedAlgebra | Aのregistered gradingとN.IsHomogeneous |
| AperyTopDegree | actual最高次数νの実現・非零次数の特徴付け・上界 |

構造・基底・積は非自明な可換係数環で構成する。
次元・Artin性の主張は任意体に対するもの。
原稿のlength Q=mに対応する数値として総k次元を証明しており、一般の `Module.length` との同定は別定理としては形式化していない。

## 再現と具体例

```sh
python3 scripts/verify_block11.py
```

このクラウドでは `PATH=/tmp/ns-p14-lean/bin:$PATH` を先頭に付ける。
26コマンド：build、12ソース再検査、新テスト、旧10Block回帰、2監査。
新規120宣言（81定理・29定義・9instance・1abbrev）と旧323件、計443件の公理依存を検査する。
graded algebraやArtinianなど、証明を含むinstanceも検査対象。
propext・Classical.choice・Quot.sound以外の依存と警告を拒否し、旧29ソース・10テスト・固定環境3個の42hashを照合する。

実例はℕ（m=1、dim Q=1、高次0）、S={0,4,5,8,9,10}∪[11,∞)（⟨4,5,11⟩）、
およびordinary半群{0}∪[3,∞)（m=e=3、δ=0、dim Q=3、q₁=2、Q₂=0、ν=1）。
後者のactual Apéry集合は{0,5,10,11}、e=3、δ=1、ν=2、Hilbert関数は(1,2,1)。
Aで非零な[15]がNに入り、Qでは0になることを検査する。
Qでは[5]²=[10]≠0、[5][11]=[11]²=0。後二つは任意体で検査する。
次数2の同型がactual quotient mapであることも具体例で確認する。

## 残る接続

今回は代数的半群環k[S]に由来するG/A/N/Qである。
完備半群環k[[S]]とのassociated graded比較は別工程。
同jump stratumのS₀加群同型、jump≤ν、A・N・T全体の有限性に必要な追加構成、
least-offset・cut・towerからactual資源の構成、最大actual Q₂からSidon pairデータへの橋、
Koszul/Torとtarget Betti公式、P14全体は未完である。
今回のQの有限性をA・N・Tすべての有限性へ読み替えず、global T≅Nの加群同型も主張しない。
原稿へ反映する証明と境界は対応台帳A18–A22に保存する。
