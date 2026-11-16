# 実行スレへの指令：Run15 / actual Tor・算術列target・ordinary全行閉鎖

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun15として、Run14の同じcut/tower/資源からactual Tor評価を証明し、真正な算術列のBetti公式・actual interval targetへ接続して、ordinary枝の全Betti行を任意体で閉じる。

**Architecture:** 同一の`Ordinary.ActualWitness`を入口に、有限長P加群のharmonic評価→実towerの三段Tor鎖→相対Rから全e変数への比較→actual targetの順に接続する。数値上界は再実装せず、Run14の`ActualWitness.all_rows`とBlock01–07を使用する。算術列は後続W_EDGEのsourceにも使える一般形で形式化する。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python検証。

**Spec:** [全体20 run計画](2026-11-10-p14-20-run-roadmap.md)、[Run14後の再校正](../../RUN14_20RUN_RECALIBRATION_JA.md)、V02 §1.2–1.3・§§6–8・ordinary閉鎖、V03 `X_AP_BETTI`・`X_AP_CONE`・`I_TARGET`・`O_HARMONIC`・`O_TOR`・`O_TARGET`・`O_CLOSE`。`O_LOW`・`O_SCALAR`・`O_SMALL`・`O_LARGE`は既存数値部をactual接続して閉じる。

## Global Constraints

- 指令作成時の公開work：`fbfa5debe3daa115b610ecc72dedc8fd52a817ca`。Run14 COMPLETE版であり、途中版`8040c90`だけを入口にしない。Run13の再現手順修正`aa6bf4c`も統合済み。
- 着手時に最新work・監査修正・`RUN14_CLOSURE_STATUS.json`・`RUN14_REMAINING_DECLARATIONS_JA.md`・検証入口を確認し、実際の基準SHAを記録する。本指令は公開実装の記録を参照して準備したもので、Run14の独立監査合格を認証しない。
- Run14の資源・cut・towerの必要入力が不足していれば同じrunで補う。完了フラグを証明として使わない。新しい監査指摘が届けば取り込む。
- 小補題・ファイル・途中コミットでrunを終了しない。実装、actual接続、修正、必要な検証、原稿台帳、監査引継ぎ、通常Pushまで一つの長いrunで進める。30〜60分を硬い上限にせず、context圧縮後も継続する。
- 固定環境・既存証明・過去の検証とZIPを保持する。許容依存は`propext`・`Classical.choice`・`Quot.sound`のみ。公刊定理名をaxiom、未証明structure field、比較結論そのものを入力にしたconstructorで済ませない。
- 今回のordinary sourceの完成範囲はe≥3、actual幅w≥m−1、全行、任意体。e=1/2・狭幅の主比較は後続の担当。ただし算術列の共通exportはd≥1を含み、target専用のd=1へ縮めない。
- 原稿と異なる十分な代替証明は可。使う仮定・到達する結論・省いた恒等式を台帳へ記録し、元の恒等式まで証明したとは報告しない。

## Review Focus

1. **環を三つ区別する。** 有限長層はP=L[λ₁,…,λᵣ]、sourceの相対環はR=L[x,λ₁,…,λᵣ]、intrinsic Bettiは全e変数環。`cutG`をP有限生成又はk有限次元と無条件に扱わない。
2. **topと次数0を保持する。** 有限長P加群のcᵣᴾ=0と、sourceのcᵣᴿ(G)を混同しない。Rはr+1変数なので必要な末端はcᵣ₊₁ᴿ(G)=0。j=1ではc₀=極小生成元数、全変数への移行ではH₀の定数補正を省かない。
3. **同じwitnessを使う。** Run14で選んだ拡大体L・cut・P・tower・Hだけを用いる。同jump同型の次数差sを保ち、globalなT≅Nを仮定しない。
4. **任意標数の実rank評価を行う。** ±1 minorは実行列で示す。有理重みj/(t+j)は整数rankの数値評価であり、係数体で分母を割らない。後続微分の消滅や任意商のBetti単調性を仮定しない。
5. **actual targetと真正な最小表示を保つ。** source・target・相対環の変数数を区別する。一般APの最小性・gcd、ideal/quotientの添字差、Dの剰余端点、範囲外0、有限体からの下降を検査する。

---

## Task 1：actualインターフェースと相対環を固定する

**Existing inputs:** `NSP14/Ordinary/ActualWitness.lean`、`Semigroup/CutAction.lean`・`FixedTower.lean`・`CutGeneratorCount.lean`、Run13のKoszul/Tor・有限性・graded比較・体拡大。

**Files:** `Ordinary/RelativePresentation.lean`、`Homological/BettiEuler.lean`等。以下の新しいファイル名・宣言名は設計候補で、既存APIとの照合後に統一する。既存宣言を作り直さない。

- [ ] kと任意の`W : ActualWitness k`から、S=`W.source`、e=`S.embeddingDimension`、e≥3の証明=`W.embedding`、L=`InfiniteScalarField k`、C=`W.cut`、r=`S.actualCutRank`を固定する。Pは既存`S.CutPolynomialRing L`。
- [ ] Rを例えば`MvPolynomial (Option (Fin r)) L`で構成し、noneをactual x、some iを同じcutのλᵢへ送る。全e変数表示への実準同型と、xとλの独立性を証明する。
- [ ] Run14にはP→S₀の単射性exportはまだない。Pを文字通り部分環と同一視するconsumerでは、線型独立な形式列と基底拡張からその同定を証明する。形式的P上の検証済み作用だけで足りる箇所へ不要な単射仮定を追加しない。
- [ ] 非x一次空間のλ列を基底へ拡張し、残りf=e−r−1個の変数Zと、元の全e変数環との実線型変数変換を構成する。その変換で通常Tor/Bettiが保存されることを証明する。
- [ ] GのR有限生成、A/T/Xₛ/Mₛ/Kₛの必要なP有限生成と有限長、対応するgradingをactual作用から供給する。Gのk有限性や、λだけに制限したGのP有限生成を入力として足さない。
- [ ] `c_j`は指定した環での通常Betti列の整数部分交代和として定義する。利用するrank-zero・非負性・末端消滅はactual対象へ証明して適用する。Run13の`partialEuler_syzygy`はexact有限ベクトル複体への定理であり、それだけでactual Betti列へ適用済みとはしない。
- [ ] 必要な最小解消・局所化の入力が不足する場合は構成するか、actual Koszul・graded Euler等による十分な代替を証明する。与えられた`MinimalFreeTower`の比較と、任意対象に対する存在を混同しない。

**Acceptance:** 同じWからP層とR-sourceの通常Torを作れること、Rの変数数r+1・全環e・残りfをコンパイル検査する。自由Pのc₁=−1という既知の対照を保ち、無条件の非負性へ一般化しない。

## Task 2：一般算術列の実Betti公式とactual interval targetを閉じる

**Files:** `ArithmeticSequence/Presentation.lean`・`Resolution.lean`・`TangentBetti.lean`、`Semigroup/IntervalCompletion.lean`、`Target/IntervalBetti.lean`等。公刊入力の証明単位とactual targetへの代入を分ける。

**Produce:** `X_AP_BETTI`・`X_AP_CONE`、actual interval容量`I_TARGET`。後続の完全AP sourceも利用できるexport。

- [ ] m≥2、d≥1、v≥1、gcd(m,d)=1、真正な最小生成系〈m,m+d,…,m+vd〉をactual数値半群として構成する。例えば1≤v≤m−1からcofinite性・最小性・原子数v+1を証明する。
- [ ] Gimenez–Sengupta–Srinivasan Theorem 4.1とHerzog–Stamate Proposition 2.5の使用する型と仮定を原典で確定する。一般APについて実解消のexactness・極小性・rank、又は同等の実Koszul計算を形式証明し、通常Bettiへ接続する。
- [ ] 代数的半群環と接錐のBetti一致を証明する。両環の同型を仮定せず、完成接錐への移行はRun12–13の実比較を使う。d=1だけを証明して一般公刊入力を閉鎖したと表示しない。
- [ ] sourceの最小原子からactual幅wとinterval completionを構成する。生成区間全体の半群と、v=min(w,m−1)の最小原子m,…,m+vによる半群が一致することを証明する。単なる仮想プロフィールをtargetにしない。
- [ ] m=av+b、1≤b≤vの規約とD=v−((m−1) mod v)=v−b+1を接続する。全i≥1について
  `F_i = i*choose(v,i+1) + (if i≤D then (D+1−i)*choose(v,i−1) else (i−D)*choose(v,i))`
  をactual targetのBettiと同定する。第0行1、i>vの0、減算の前提を明示する。
- [ ] `Fmin_i(v)=i*choose(v,i+1)+min(choose(v,i−1),choose(v,i))`、その下界性と幅方向の単調性を証明する。V02のTLOWの必要行も供給し、後続の幅側が再利用できるようにする。
- [ ] ordinaryではv=m−1、全i≥1でactual targetのBetti=`i*choose(m,i+1)`を得る。数値式の定義とactual Bettiの定理は別にする。

**Acceptance:** v=1、D=1/v、i=D/D+1、i=0/v/v+1、d>1の真正AP、標数2を含む任意体で検査する。m=1にvでの除算を適用しない。既存の一般AP APIがあれば再利用し、その仮定と全行の型を記録する。

## Task 3：初期加群と実minorからharmonic Koszul評価を証明する

**Files:** `Homological/InitialModule.lean`・`KoszulInitialRank.lean`、`Ordinary/HarmonicRank.lean`等。Run13の`StandardMonomials.lean`・`MinorRank.lean`を利用し、不足する有限自由加群版を補う。

**Produce:** 単一次数bで極小生成される有限長P加群Z、hₜ=dim Z_(b+t)に対し

`c_j^P(Z) ≤ choose(r−1,j) * Σ_t (j/(t+j))*h_t`（1≤j<r）、
`c_0^P(Z)=μ_P(Z)`、`c_r^P(Z)=0`。

- [ ] 同shiftの実表示P^q→Zと実kernelから初期部分加群を構成し、商の標準単項式基底・各次数の次元保存を証明する。scalar ideal用の結果だけでmodule版も完了とはしない。
- [ ] 同じラベル順の実Koszul境界行列をblock三角化し、`R_i(Z) ≥ R_i(Z*)`を証明する。抽象的なrank不等式を未証明の入力にしない。
- [ ] 単項式商で、v∉Fのtarget `(m,F)`とsource `(m/x_v,F∪{v})`を対応させる。存在する単項式・重複の排除・実対角±1 minorを証明する。
- [ ] 多重次数αの`α_v/(t+j)`を有理数として平均し、整数rankの下界を得る。有限台と分母正値を証明して和をとる。正標数の体内で分母を逆にしない。
- [ ] 有限次元Koszul鎖のEuler計算から
  `c_j^P(Z)=choose(r−1,j)*length(Z)−R_(j+1)(Z)`
  を接続し、harmonic評価・j=0・j=rを閉じる。
- [ ] Run14の同じCのXₛとMₛへ、既存の単一次数生成性・augmentation商と底次数の同型を実際に適用する。

**Acceptance:** 自由表示の生成元数q>1、非単項式kernel、非零の微分rank、標数2、零加群、hの途中の零、topを検査する。有限サンプルや±1 minorの一般補題だけではO_HARMONIC完成としない。

## Task 4：actual towerから三段のTor鎖と既存rowへの上界を得る

**Files:** `Ordinary/TorChain.lean`・`RelativeKoszul.lean`等。

**Existing inputs:** `C.cutTower_exact`、`C.sameJumpCutIso`・`sameJumpCutIso_degree`、`towerX_top_zero`、`cutTower_generated`、`cutGeneratorQuotientEquiv`、Run13の実LES・connecting rank。

- [ ] 0→K→M→L→0の実LESから、整数部分交代和について
  `c_j(M)=c_j(K)+c_j(L)−d_(j+1)`、
  `c_j(K)=c_j(M)+c_(j+1)(L)−(β_(j+1)(L)−d_(j+1))`
  を証明する。connecting rankとその補数の両方が非負であることを示し、二つを同じrankと呼ばない。
- [ ] x-KoszulのA/Tから、R上のGの実比較を構成する。V03 O11のd₂補正を使うなら実connecting/differentialから構成する。十分な有界filtration比較で代替する場合も、必要な交代和不等式を証明し、d₂=0や退化を入力にしない。
- [ ] B=A/X₂を実商として構成し、P加群として`P/P_+² ⊕ k(-1)^(e−r−1)`に同定する。Lⱼ=`TargetMargin.lower e r j`がこのBのcⱼであることを証明する。
- [ ] 1≤j≤rで次の三段を実対象のまま証明する：
  `c_j^R(G) ≤ L_j+c_j^P(X₂)+c_(j−1)^P(T)`、
  `c_(j−1)^P(T) ≤ Σ_(s=2..ν)c_(j−1)^P(K_s)`、
  `c_(j−1)^P(K_s) ≤ c_(j−1)^P(M_s)+c_j^P(X_(s+1))`。
- [ ] 同jump同型は第2段で使い、全体のT/Nを同型としない。X_(ν+1)=0で端を消し、j=1ではc₀(Mₛ)=実際の極小生成元数を保持する。
- [ ] Task 3とRun14の同じHを使って、全1≤j≤rについて
  `(c_j^R(G) : ℚ) ≤ TargetMargin.lower e r j + (S.actualLayers k).row r j S.deficit`
  を証明する。Wⱼの式は既存`LowRank.weight`へ等式で接続し、t=0/1、j=1、j=rの境界を照合する。
- [ ] `W.all_rows`又は`W.numericalData.relative_rows`へ適用し、実cⱼᴿ(G)≤既存のRⱼを得る。新しい任意c列を仮定して終了しない。

**Acceptance:** δ=0の空塔、非零T、jumpの異なる例、同jumpの+s、r=2/3、j=1/r、非零のconnecting補正を検査する。topのcᵣᴿ(G)を0と仮定しない。

## Task 5：第0 homologyの補正を保持して全e変数のBettiへ移す

**Files:** `Ordinary/FullBettiTransfer.lean`・`Target/CoefficientComparison.lean`等。

**Produce:** q=e−r、f=q−1、C(z)=Σ_(j=1..r)cⱼᴿ(G)z^jに対して、係数ごとの不等式

`B_G(z) ≼ T_(q+1)(z)+(1+z)^q*C(z)`、
`T_m(z)−T_(q+1)(z)=(1+z)^q*Σ_(j=1..δ+r−1)R_j*z^j`。

ここで`T_n=1+Σ_(i≥1)i*choose(n,i+1)z^i`、Rⱼは既存`TargetMargin.target e δ r j`。

- [ ] actual `H₀(K_R(G))=G/(x,E)G`を、残りf変数が作用する`L[Z]/(Z)²`と同定する。単なる次元f+1で済ませず、この同じZ作用について同定する。
- [ ] actual R-Betti多項式`B_G^R=(1+z)((f+1)+C(z))`に必要な末端・有限性を証明する。高次行とH₀を分けた実有界二重複体又は十分なfiltration比較を作る。
- [ ] `B_G ≼ T_(f+1)+(1+z)^f*(B_G^R−(f+1))`を証明する。引く定数f+1がH₀の補正であることを保持し、`T_(f+2)−T_(f+1)=(f+1)z(1+z)^f`で上の形へ直す。
- [ ] hockey-stick/係数畳み込みからtarget差の恒等式を証明し、既存のRⱼの定義と一致させる。余るj>rの係数は非負として扱い、自然数の切捨てで差を隠さない。
- [ ] Task 4のcⱼ≤Rⱼを係数ごとの比較へ適用し、全i≥1でactual sourceのintrinsic Betti≤`i*choose(m,i+1)`を得る。relative rowの範囲i≤rだけを最終結果にしない。

**Acceptance:** f=0（r=e−1）、δ=0、i=0、i=e、i=m−1/m、relative topの非零例を検査する。第0 homologyを全て鎖群の次元で上から抑えた粗い式を、補正済みO14と同じものとして使わない。

## Task 6：任意体・actual completionのordinary主定理をexportする

**Files:** `Ordinary/Closure.lean`・`Target/ActualComparison.lean`等。

- [ ] 拡大体L上の同じWで得た比較を、Run13のactual source/targetのfull Betti体拡大保存で元のkへ戻す。cutそのものが有限体k上へ下降するとは主張しない。
- [ ] Sのactual幅w≥m−1から、actual interval completionのtargetがTask 2のordinary targetになることを証明する。sourceはe変数、targetはm変数の真正な最小表示を使う。
- [ ] 意味上の最終exportを次の二つとして揃える（名称は既存APIに合わせて確定する）：
  `ordinary_betti_bound S k he hwide i hi`：全i≥1で、actual Gのfull totalBetti≤`i*choose(S.multiplicity,i+1)`。
  `ordinary_actual_completion_betti_le S k he hwide i`：全i≥0で、literal完成半群環のactual接錐のBetti≤actual interval completionの完成接錐のBetti。
- [ ] 第0行は両側1を証明して補い、上端より後の0も含める。Run12–13の自然な完成接錐比較を実際に適用する。
- [ ] 最終定理の引数・instanceにcut存在、資源上界、harmonic rank、公刊Betti公式、Tor-to-row、target同定、解消exactnessなどの未証明Propが残っていないことを確認する。

**Acceptance:** r=2のΓ=〈6,7,11〉、δ=0、非零Tを持つΓ=〈9,10,15,26〉等の実例、標数2・有限体拡大、ordinary targetの全行をコンパイル検査する。sourceがordinary半群そのものである場合だけを証明して、w≥m−1のsource全体を閉じたとしない。

## Task 7：検証・原稿対応・監査引継ぎ・公開

- [ ] 上の各Taskで先に受入型と期待する等式/不等式を固定し、未実装で失敗することを確認してから実装する。汎用理論は今回と後続が実際に使う範囲に絞る。
- [ ] 実装順は依存で調整してよい。AP/targetとharmonicは同じrun内で進め、片方だけの途中公開でRun15全体の完了にしない。
- [ ] `tests/ArithmeticSequenceBetti.lean`・`HarmonicRank.lean`・`OrdinaryTor.lean`・`OrdinaryClosure.lean`等に、一般定理の適用・境界・非零写像の検査を置く。ファイル名は候補。
- [ ] `scripts/verify_run15.py`等は実際のfixture依存順で実行し、試験専用mathlib importもビルドする。空のproject test cacheから全受入を通す。旧Runの検証スクリプトを新しいソース集合にそのまま実行せず、固定した過去commitの記録又は依存を解決した回帰入口を使う。
- [ ] 全新規宣言・instance・constructor/recursor/自動生成宣言とroot-moduleの公理依存をLean環境から抽出し、追加数学公理・自己依存を拒否する。新規宣言の通常/explicit型、所属module、仮定を保存する。必要な旧Block01–14の回帰・監査境界・固定hashも確認する。
- [ ] `verification/run15/`、COMPLETE又は正直なPARTIAL ZIP、source/evidence hash、`RUN15_CLOSURE_STATUS.json`・未完宣言一覧、進捗と原稿台帳を確定する。過去の原本を上書きしない。
- [ ] 原典のAP証明・初項rank・有界比較とactual入力の対応を記録し、監査側が各前提の供給元と最終定理の型を追えるようにする。
- [ ] 通常commit/Push後、remote SHAとclean worktreeを確認する。最新workを取得するときは明示的に`refs/heads/work:refs/remotes/origin/work`をfetchするかFETCH_HEADを確認する。並行更新があれば保持して統合し、force Pushしない。

## 終了条件と後続run

**同じactual witnessから通常Torの上界・actual targetのBetti・全行比較・任意体への下降まで実証明でつながった時にRun15完了とする。**
公刊入力の名前だけ、正しい数値プロフィールだけ、条件付きのTor-to-row、d=1専用公式、top/第0行を落とした比較だけでは、この指令の全体完了条件を満たさない。
必要な基礎入力の不足は同じrunで補い、実際に解けない障害があれば、閉じたexport・残る正確な型・理由・必要入力を保存する。

20 runは運用目標。Run15の実測を用いて残りRun16–20の配分を再校正する。
狭幅の端点core/移行、Kneser/SC、BHP/EK、N4/LTV、全域合成は引き続き後続の担当であり、予定数のために未完を隠さない。

このファイルは実行スレへ貼り付け/参照するための指令である。監査スレからの直接送信やRun15の証明実装は行っていない。
