# 実行スレへの指令：Run17 / Kneser・Savchev–Chenと実coreへの接続

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun17として、合成数位数を含むKneser和集合定理・反復形と、長零和自由列のSavchev–Chen unit正規化を実証明し、Run18の疎幅/四点成長とRun19のN4がそのまま使える群・列・actual coreのexportを揃える。

**Architecture:** 和集合・安定化部分群・有限商の共通APIを固定し、Kneser本体→反復→巡回群の成長を接続する。列は位置付きのまま扱い、SCの実unitと自然数代表和を構成する。最後にRun16の同じ正規化offset・最短距離・QCへ適用し、公刊定理の結論そのものをconsumerの仮定に残さない。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python検証。

**Spec:** [全体20 run計画](2026-11-10-p14-20-run-roadmap.md)、[Run16後の再校正](../../RUN16_PLAN_RECALIBRATION_JA.md)、[V03依存表](../../../proof_structure_v3/P14_DEPENDENCY_MAP_V03.md) `X_KNESER`・`X_SC`とconsumer `W_SPARSE/W_FIVE/N_DISTANCE/N_WORDS`、[V02](../../../proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md) §1.2(3),(6)、§13.4–13.5、§14.2–14.3。

## Global Constraints

- 作成時の公開workは`584f92d8c1a7fc1e2413f606b661fc9b81f472cd`。Run16の独立監査は[commit 5ced6cc](https://github.com/stksk310/NS-P14-Lean/blob/5ced6cc/audit/run16_independent/README_JA.md)で指定11 ID合格。着手時に最新work・監査修正・実exportの型を確認し、採用SHAを記録する。
- 担当閉鎖IDは`X_KNESER`と`X_SC`の二つ。既存の数値回帰や群の基礎APIだけでは閉鎖に数えない。有限表、原典名のaxiom、結論を保持する未証明structure field、同じ結論を引数にしたwrapperで済ませない。
- 一つの長いrunで、両公刊入力の証明、必要なconsumer接続、修正、全検証、原稿台帳、監査引継ぎ、通常Pushまで進める。片方・小補題・内部commitで終了しない。30〜60分を硬い上限にせず、context圧縮後も継続する。
- 20 runは運用目標。新しい公刊証明の形式化は独自の依存証明を要する。run数を守るために範囲を素数だけ・二種類の項だけへ縮めたり、未証明を完了に数えたりしない。実際の障害は未完の正確な型とともに保存する。
- 固定toolchain/mathlib、Run01–16の数学sourceと検証原本・ZIPを保持する。許容依存は`propext`・`Classical.choice`・`Quot.sound`のみ。依存更新で未確認の定理を持ち込まない。
- Kneserの共通本体は有限可換群上に置き、有限商群へ適用できるようにする。無限ambient群への一般化は今回の必要条件ではない。SCの必須出口はすべての正位数巡回群の長零和自由列であり、単なる長さ上界や二値列専用結果に代えない。
- Run18のBHP/EK、幅側のtarget支払いや全域閉鎖、Run19のN4のsocle三角形・混合語の最終計数/LTV、Run20の全域合成は担当を保持する。本runの群成長・距離・適用補題を、それら全IDの完成と表示しない。
- 以下の新規ファイル名・宣言名は設計候補。入口と結論の意味を保ち、実際のmathlib/既存APIに合わせて統一する。別の十分な実証明を採用した場合は原稿との差と供給する結論を記録する。

## Review Focus

1. **nAの意味と境界。** n個の独立な選択の和集合で、0A={0}。点ごとのn倍写像の像と混同しない。二集合版は両集合非空、反復版はn≥1。全群への飽和・自明群・n=0/1も処理する。
2. **合成数と実stabilizer。** Hは実際の和集合の加法安定化部分群。商の非周期性、部分和のstabilizer包含、coset数と|H|の積を証明する。素数版Cauchy–DavenportやEGZをKneser/SCの代わりに使わない。
3. **列の重複と厳密な半分境界。** 零和自由性は非空の位置部分集合すべてについて定義する。値集合へのdedupは禁止。SCの長さ条件は`u < 2*ℓ`であり、等号へ緩めない。
4. **unitと代表和。** unitは`(ZMod u)ˣ`、結論は全位置の最小正代表のNat総和<u。ZMod内の総和条件と取り違えず、各項の非零性・代表の正値性・unitの逆を供給する。合成数の`ZMod u`にField instanceを要求しない。
5. **同じ正規化core。** 剰余の法は正規化幅uであり、sourceのmultiplicity mでも係数体の標数でもない。集合は正規化offset a_iで作り、物理offset d*a_iへ置換しない。SC unitは列の補助操作であり、actual sourceの変換・反射・R/Hx保存を意味しない。

---

## Task 1：共通定義・原典・凍結した受入命題を固定する

**Files:** `NSP14/Additive/Sumset.lean`・`Stabilizer.lean`・`ZeroSumSequence.lean`・`UnitRepresentatives.lean`、`audit/run17/RequestedGoals.lean`。

**Consumes:** mathlibのpointwise Finset、加法部分群・商群、ZMod、有限和。Run16の`Endpoint.Data`、`shortestDegree`・`wordVolume`、`CoreMinimal`・`internalPoint`、実QC作用。

- [ ] 固定版の意味上のAPIを再確認する。`Combinatorics/Additive/ETransform.lean`、`CauchyDavenport.lean`、`VerySmallDoubling.lean`、`SubsetSum.lean`、`ErdosGinzburgZiv.lean`は基礎候補。今回の検索では正確なKneser/SCの証明は確認できていない。名前が似た定理は型と量化を読んでから使う。
- [ ] [DeVos Theorem 1](https://www.sfu.ca/~mdevos/papers/kneser.pdf)と[Savchev–Chen math/0602568v1 §4 Theorem 8](https://arxiv.org/html/math/0602568v1)の本文・必要な先行補題を確認し、取得先、version、取得できた本文のhash、使用命題とLeanで証明する依存単位を台帳へ記録する。原典が取得できない場合も、結論を公理化しない。
- [ ] `iteratedSum A 0={0}`、`iteratedSum A (n+1)=iteratedSum A n+A`を定義する。`sumStabilizer S={h | h+S=S}`は実`AddSubgroup G`として構成し、既存の加法作用stabilizerとの同一性を供給する。`thicken A H=A+H`の有限集合を定義する。
- [ ] canonicalな列は`seq : Fin ℓ → ZMod u`とする。`ZeroSumFree seq := ∀ I : Finset (Fin ℓ), I.Nonempty → ∑ i∈I,seq i≠0`を定義する。位置の置換、部分列、unit倍に対する保存と、List/Multisetへの必要な変換を証明する。値をFinset化しない。
- [ ] `positiveRep`は非零な剰余の標準Nat値、`representativeSum c seq=∑ i,(c*seq i).val`とする。u>0の`NeZero`/Fintypeと、u=0では有限巡回群のAPIを使わない境界を固定する。u=1はSCのlong零和自由列が存在しないことを別に処理する。
- [ ] 元の必須二命題をPropの定義として凍結する（未証明の定義は完了ではない）。Kneserは有限可換群のすべての非空A,B、SCはu≥2・全ℓ・全ZeroSumFree列・`u<2*ℓ`について、下記の結論そのものを要求する。後の`ClosedGoals.lean`が同じ命題を追加前提なしに閉じる。

**Acceptance:** `tests/Run17Definitions.lean`でn=0/1、ZMod 6のA={0,1}に対する2A={0,1,2}と点ごとの倍像{0,2}の相違、空列の零和自由性、列[2,2,2] mod 6の`¬ZeroSumFree`を名前付き定理で検査する。

## Task 2：有限可換群の実Kneser定理を証明する

**Files:** `NSP14/Additive/KneserCore.lean`・`Kneser.lean`、必要なe-transform/period補題ファイル。**Test:** `tests/KneserActual.lean`。

**Produce:** 有限可換群G、非空Finset A,B、`H=sumStabilizer(A+B)`について

`(thicken A H).card+(thicken B H).card ≤ (A+B).card+Nat.card H`。

- [ ] 上の型を固定し、未実装の公開宣言を参照する受入が失敗することを保存する。Hを任意の有利な部分群へ選び直さず、結論を前提として渡さない。
- [ ] 原典の有限群の場合の実証明を実装する。使うtransformの和集合包含・cardinality保存、帰納パラメータの真の減少、periodic/critical caseの部分群・coset補題を実際のFinsetへ証明する。有限群全列挙を全位数の証明としない。
- [ ] 引き算は上の加法形、又はIntで管理する。`|A+B|≥|A|+|B|−|H|`だけの弱い形で止めず、A+HとB+Hを持つ必要な形を得る。
- [ ] ZMod u（u>0）への公開wrapperと、自明stabilizer、和集合=全群、trivial groupの場合をexportする。合成数位数のまま適用できる型を確認する。

**Acceptance:** ZMod 8、A=B={0,1,4,5}でA+B={0,1,2,4,5,6}、実H={0,4}、補正後の下界6が等号になることを証明する。無補正の7下界は偽であることも検査する。singleton、全群、u=1、素数位数も含める。

## Task 3：商群での反復とconsumer向け巡回成長を閉じる

**Files:** `NSP14/Additive/KneserIterated.lean`・`CyclicGrowth.lean`・`FourPointGrowth.lean`。**Tests:** `KneserIterated.lean`・`CyclicGrowth.lean`。

- [ ] 任意の部分群Hと商写像πについて、`|(A+H)|=|H|*|π(A)|`を実coset/fiber計数で証明する。Hで飽和したSのcardと商card、商のstabilizerの正確な同定を供給する。
- [ ] `H=stab(nA)`、n≥1のとき、商でnĀが非周期的であり、1≤j≤nの部分和のstabilizerもその中に入ることを証明する。単に「商だから非周期的」と仮定しない。
- [ ] 二集合版を商で反復し、全n≥1で
  `n*|(A+H)| ≤ |nA|+(n-1)*|H|`、H=stab(nA)
  を得る。n=0はcard 1の別の出口を用意する。
- [ ] ZMod u、0∈A、Aが加法群全体を生成、a=|A|≥2、s=ceil(a/2)=(a+1)/2に対して、(n+1)Aが真部分集合ならn≥1で増分≥sを証明する。実Hのcoset数cはc≥2・c|H|≥aを満たすことを示し、全n≥1で`|nA|≥min(u,a+(n-1)s)`を得る。
- [ ] 0<a<b<u、gcd(a,b,u)=1について、0を含む三点集合の全n≥0で`|n{0,a,b}|≥min(u,2n+1)`をexportする。a又はbが個別にunitであるとは要求しない。
- [ ] 四点の群補題を供給する。u≥8、0∈A、|A|=4、生成性、n≥1の下で、(n+1)Aがproperで増分が3未満なら位数2のHの二cosetをAがちょうど占めることを証明する。巡回群で`u=2h, A={0,t,h,t+h}, 0<t<h, gcd(t,h)=1`へ直し、非antipodalなら全n≥0で`|nA|≥min(u,3n+1)`を得る。対応core/Artin計算とW_FIVE閉鎖はRun18に残す。

**Acceptance:** ZMod 6の{0,2,3}で到達card列1,3,5,6を検査する。ZMod 8のantipodal {0,1,4,5}は最初の増分2、非antipodal {0,1,2,4}はproperな最初の増分3。奇数/偶数aでceilを検査し、n=0/1、飽和前後、非自明H、H=全群を含める。

## Task 4：長零和自由列のSC unit定理を実証明する

**Files:** `NSP14/Additive/SavchevChenCore.lean`・`SavchevChen.lean`と原典の必要補題。**Test:** `tests/SavchevChen.lean`。

**Produce:** u≥2、`seq : Fin ℓ → ZMod u`、`ZeroSumFree seq`、`u<2*ℓ`から

`∃ c : (ZMod u)ˣ, ∑ i : Fin ℓ,(c*seq i).val < u`。

- [ ] 型を凍結し、公開証明がない段階の失敗を記録する。結論に同じcを全項へ作用させる。項ごとに別のunitを選ばない。
- [ ] 基礎として全項非零、位置付きprefix和の単射とℓ<u、部分列/置換/unit倍による零和自由性保存を証明する。これらだけでX_SCを閉鎖したとしない。
- [ ] 原典Theorem 8とそれに必要な先行補題の実証明を形式化する。補助的な正規形、列の分割・圧縮・帰納を使う場合は、長さ・重複・非空選択和を保持する写像を示す。生成性等を途中で仮定する場合はlong条件から供給し、最終型へ追加しない。
- [ ] 代表の和はNat/Intで持ち、mod uの和から総和の小ささを飛躍しない。全位置で`0<(c*seq i).val<u`と、自然数和がu−1以下という利用形をexportする。u=1/2と空列の境界を別途閉じる。
- [ ] 一般列の必須定理から二種類の項の利用形を導く。α≠β、両個数R,T≥1、R+T>u/2で、その二値列が零和自由である場合、必要に応じて二ラベルを交換し、同じunit倍後に一方の代表が1、他方がc₀≥2、`R+c₀*T≤u-1`となることを証明する。元の群で`(c₀ : ZMod u)*α=β`というmodular relationも返す。これはactual sourceのunit変換ではない。

**Acceptance:** u=6の[5,5,5,4]は零和自由・長さ4でunit 5が代表和5を与える。u=9の[2,2,2,4,6]は三種類・非unitの項を含む零和自由列で、unit 5が代表和8を与える。u=6の[2,2,3]は長さちょうどu/2で零和自由だが、全unitの代表和は7又は11であり結論が偽。厳密閾値、重複、u−1個の同じunitの列、u=1/2/3を検査する。

## Task 5：Run16の同じcoreへ適用し、後続の入力を実exportにする

**Files:** `NSP14/Additive/EndpointResidues.lean`・`EndpointDistance.lean`・`StandardWordSequence.lean`。**Tests:** `EndpointAdditive.lean`・`StandardWordZeroSum.lean`。

- [ ] D : `Endpoint.Data`からZMod D.uの実集合`A={0}∪image(a↦(a:ZMod D.u),D.a)`を構成し、card=D.q+1、0∈A、全群生成を証明する。原子の物理offset d*aを使わない。`D.offsets`のmod u像もこのAと一致することを示す。
- [ ] Run16の実語・`shortestDegree`へ接続して、全n≥0で`r∈nA ↔ D.shortestDegree r≤n`を証明する。0のpadding、全剰余の到達、`shortestDegree<u`を保持する。
- [ ] 実際の`D.wordVolume`について有限尾和
  `W=1+Σ_(n=0..u-1)(u-|nA|)=u+Σ_(n=1..u-1)(u-|nA|)`
  を証明する。定数1とn=0を落とさず、無限和の有限台を未証明にしない。
- [ ] Task 3を適用し、s=ceil((q+1)/2)=(q+2)/2（最後はNat除算）として
  `D.wordVolume ≤ D.u+Σ_(j∈range D.u)(D.u-(D.q+1)-s*j)`
  を証明する。右辺のNat減算は正部分。q=2には`D.wordVolume≤1+(D.u*D.u)/4`を実際にexportする。疎幅の剰余多項式・B≤u²/(e−1)・target支払いはRun18、socle三角形とN_DISTANCE全体はRun19に残す。
- [ ] QCで生存する純内部語から、同じ正規化offsetの位置付き零和自由列を作る。任意の非空位置部分集合の整数offset和がKuなら、1≤K≤長さ−1と実coreの端点因子表示を証明し、QCで0になることを用いる。prefixだけでなく任意の位置選択を覆う。
- [ ] q=2の混合語への型付きconsumerを揃える。実QCの生存条件→零和自由列→long条件ならTask 4のunit・代表和・二ラベル関係、までを追加のSC Propなしで適用できるようにする。`R<c₀`の端点関係、混合語長≤u/2、P/Hxの最終計数と全行target比較はRun19で閉じる。

**Acceptance:** Run16の(m,d,a,u)=(7,2,{1,3},4)で、正しいAのcardは3であることを検査する（d*aへ変えると生成性を失う）。(8,1,{2,3},6)で実W=10。実QCの非零語の例は(9,1,{2,3},7)の内部語[2,3]で、群の列も零和自由であることを証明する。すべての適用は元のDを保持し、R/Hxの反射不変性を新たに仮定しない。

## Task 6：全回帰・公理監査・原稿台帳・公開

- [ ] 各Taskは先に受入型を固定して失敗を記録し、実装後にfocused build/testを通して内部commitする。受入は名前付き定理にし、sectionの仮定が必要な場合は明示して、通常/explicit型を検査する。匿名exampleのmoduleを宣言監査の網羅性に数えない。
- [ ] 小位数の群・multisetについて独立した有限回帰を用意する。例えばu≤8の非空集合対/反復・零和自由multisetを調べ、上の具体例と厳密閾値の反例を含める。大きな表を一般証明の代用にせず、検算データとLean証明を区別する。
- [ ] `scripts/verify_run17.py --fresh-test-cache`等で、固定基準Run16までの原本をbyte照合し、全fixtureを実依存順で実行する。試験専用importを含め、空のproject test cacheと新規productionの再ビルドから検証する。旧記録の絶対出力先を再生しない。
- [ ] 全新規宣言・instance・constructor/recursor・生成helperとroot-moduleの公理依存をLean環境から抽出する。追加数学公理・自己依存を拒否し、通常/explicit型、module、source hashを保存する。Run15の元8目標とRun16の11 IDの契約も回帰する。
- [ ] `verification/run17/`、source/evidence hash、COMPLETE又は正直なPARTIAL ZIP、`RUN17_CLOSURE_STATUS.json`、未完宣言一覧、原稿台帳、監査引継ぎを確定する。verifier/packager/数値入力も束縛し、ZIPの全entry/hash/CRCを照合する。過去検証・ZIPを上書きしない。
- [ ] `RequestedGoals.lean`の元の二命題を変えず、`audit/run17/ClosedGoals.lean`で同時に証明する。群成長・実W・SC適用の主要exportも対応表へ記録する。原典どおりの証明と十分な代替を区別する。
- [ ] 通常commit/Push後、remote SHAとclean worktreeを確認する。最新workは`git fetch origin refs/heads/work:refs/remotes/origin/work`等で実際のSHAを確認する。並行更新は保持・統合し、force Pushしない。

## 終了条件

**Kneser本体・有限商での反復・合成数を含む巡回成長、一般のlong零和自由列へのSC unit定理、同じactual coreの距離/語への適用が、未証明の比較結論を前提にせず接続し、検証・台帳・通常Pushが揃った時にRun17完了とする。**

素数位数だけ、min-order下界だけ、ℓ<uだけ、二種類の列だけ、有限unit探索だけでは担当二IDの完了条件を満たさない。
実際に閉じない障害は、閉じたexport・残る正確な型・理由・必要入力として保存する。
Run17の実測で残りRun18–20の配分を再校正し、20という数のために数学的な完成条件を変えない。

このファイルは実行スレへ貼り付け/参照するための指令である。監査スレからの直接送信やRun17の証明実装は行っていない。
