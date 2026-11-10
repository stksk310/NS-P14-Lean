# 実行スレへの指令：Run14 / Green・一つのcut・actual tower・共通資源・Sidon

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun14として、Greenの必要な形式証明、一つのsquare-zero cut、least-offset安定化、actual towerと唯一の資源列、最大Q₂→Sidonの橋を閉じる。

**Architecture:** 同じactual半群・体・一度選んだcutを証明付きwitnessに保持する。Run12の座標・jump構造とRun13の必要な有限性/体拡大exportから実商と完全列を構成し、そこから数値資源の全条件を証明する。既存Block01–07は同じactual witnessから使う。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python検証。

**Spec:** [20 run計画](2026-11-10-p14-20-run-roadmap.md)、V02 §§3–5、V03 `X_GREEN`・`O_CUT`・`O_VOLUME`・`O_TOWER`・`O_SIDON`、既存`NumericalClosure.Data`と`Boundary`。

## Global Constraints

- 指令作成時点でRun13は実行中、最新公開workはRun12 `6b8d16889ea9b4d88567f0d9ac70391db2a49824`。Run13の完成・監査通過を本指令は認証しない。
- Run13を完成・検証・Pushした後に着手し、実際の基準SHAとexport一覧、未完入力を記録する。特にI_FIELDを未証明のまま有限体のcutを完成扱いしない。
- 必要な基礎入力が不足していれば同じrunで補う。解けない障害があれば正確に保存し、独立に進められるoffset/Sidon等を進める。未完があればRun14全体を完成と報告しない。
- 一つの長いrunで実装・接続・修正・必要な検証・原稿台帳・監査引継ぎ・通常Pushまで進める。小補題や内部コミットごとに終了しない。30〜60分を硬い上限にしない。
- 固定環境・過去の証明と検証原本を保持する。許容基盤は`propext`・`Classical.choice`・`Quot.sound`。追加数学公理・`sorryAx`・隠れた未証明入力で閉じない。
- cutの構成とtowerはe≥3の範囲で行う。e=1/2やr=2へ、必要条件を越えて一般化しない。offsetの数値構成は適切に退化境界も扱う。
- 原稿からの短縮や代替証明は、仮定・結論・実対象との対応を`docs/LEAN_PAPER_ALIGNMENT_JA.md`へ記録する。

## Review Focus

1. Greenは必要な任意標数の次数2特殊版を証明する。引用・未証明のcut存在・CharZeroへの限定を完成証明として渡さない。
2. 同じsource・同じ拡大体・同じcutの資源だけを使う。別cutのH₁上界と総資源を混ぜない。
3. cut環Pは独立な一次形式の多項式環として作用する。Aの中の像が代数的独立であるとは仮定しない。
4. 安定化・有限性・整数除算の前提を証明してから、有限台・finrank・自然数の差を使う。tailの台を既存scalarのcutoff以下へ制限しない。
5. maximal Q₂→Sidonはactual二次積の独立性から導く。反復項・cross-degree・標数2・合成数/偶数mを保ち、maximal-cutの系はr≥3に限定する。

---

## Task 1：入口のactual witnessと依存を固定

**Consume:** actual S、m/e/δ、G/T/A/N/Q、ν、実S₀作用、同jump商と次数差、Run13の必要な体拡大・有限性export。

**Produce:** source・体・q₂=a・cut rank r・拡大後の対象と自然写像を追跡できるwitness。

- [ ] V02 §§3–5とV03の5項目、Run13の完了/未完台帳、最新監査を読む。必要な宣言を実際にimport・適用して前提を確認する。
- [ ] `NSP14/Ordinary/ActualWitness.lean`等に責務を分ける。名称は既存APIと照合して確定し、同じ対象の重複定義を避ける。
- [ ] aはactual `qDegree 2`の次元、νはactual最高次数とする。プロフィールの数値を任意に選ぶ入口を最終constructorにしない。

## Task 2：least-offset経路・安定化・有限性 O_VOLUME

**Produce:** 各剰余ρのactual bρ、lρ、sρ、Lρと、剰余別・全体の資源恒等式。

- [ ] actual非x原子の正offset g−mによる語の存在を各剰余で証明し、最小offset bρと、その値を実現する最短語長lρを構成する。
- [ ] ωρ−bρが非負のmの倍数であることを示してLρを定義する。非零剰余で1≤sρ≤Lρ≤lρを証明する。
- [ ] least-offset prefixの最小性・剰余の無重複、e−1個のatom剰余を使い、bρ昇順のρₖでLρₖ−1≤min(δ,k−1)を証明する。
- [ ] Σρ≠0(Lρ−1)≤δ(e+δ/2−3/2)を証明する。有理数の評価と整数の量を明示して接続する。
- [ ] q≥lρ−Lρでord(ωρ+qm)=Lρ+qとなる安定化と、Σterminal τ≡ρ(jump τ−1)=Lρ−sρを証明する。terminalの有限台を先に供給する。
- [ ] 必要なA・N・Tの有限k次元/有限台をactual基底から得る。m=1の非零剰余が空の場合と、δ=0も検査する。

## Task 3：Greenの必要形と一つのsquare-zero cut

**Produce:** 必要な`X_GREEN`の実証明、r=max(2,p(a))、2≤r≤e−1、一度選ぶ独立な一次形式列E、(A/EA)≥2=0。

- [ ] 必要な次数2のGreen特殊版を、正確な仮定で形式証明する。既存の形式定理を再利用する場合は宣言・仮定・適用のコンパイルを記録する。
- [ ] a=binomial(p+1,2)+b、0≤b≤pという整数分解と、s本切断後の上界binomial(p+1−s,2)+max(b−s,0)を正確に導く。
- [ ] s=pで二次が消え、標準生成から高次も消えることを示す。p<2では独立な2本へ拡張し、e≥3を明示する。
- [ ] 有限体では同標数の無限純超越拡大とRun13のI_FIELDを使う。原体にcutが存在するとは仮定せず、拡大上で構成して後続のBetti比較を戻せる形にする。
- [ ] λ₁,…,λᵣはS₀の独立な一次形式とする。Pはそれらに対応する多項式環（S₀内の部分環又は同型な別多項式環）として固定する。Aの作用像には関係があってよい。
- [ ] 同じPへRun12のT/N、filtration、同jump商同型を制限し、実際の作用と完全列の整合性を証明する。

## Task 4：actual towerと完全列 O_TOWER

**Produce:** 同じcut上のUₛ、Xₛ、Mₛ、Kₛとactual P加群短完全列。

- [ ] FₛNをRun12のactual部分加群と対応させ、Aのactual斉次イデアルとして束ねる。Uₛ=A/Fₛ₋₁、Xₛ=(Uₛ)≥s、Mₛ=(Uₛ)≥s+1、Kₛ=Fₛ/Fₛ₋₁を実商・実次数から作る。
- [ ] 2≤s≤νで0→Kₛ→Mₛ→Xₛ₊₁→0とXν+1=0を証明する。Kₛ⊂Mₛにはhead次数≥s+1を実際に使う。
- [ ] UₛとQの低次一致、およびcutによるXₛ/Mₛの単一次数s/s+1生成を証明する。生成元数もactual quotient/次数の次元と同定する。
- [ ] δ=0では空塔と零資源列を構成する。切捨て添字で架空の非零層を作らない。

## Task 5：唯一の資源列と既存数値定理へのconstructor

**Produce:** hₛ,ₜ=dim(Xₛ)ₛ₊ₜ、Hₜ=Σₛhₛ,ₜ、有限台と全同時上界、actual `NumericalClosure.Data`。

- [ ] Apéry座標のt区間[0,sρ−2]と、次数p・jump dのterminalに対応するheadの区間[p,p+d−2]をactual towerの基底と同定する。
- [ ] 同じ剰余内で区間が互いに素であることから、H₀=δ、0≤Hₜ≤m−1を証明する。
- [ ] ΣₜHₜ=Σρ≠0(Lρ−1)≤δVを証明し、同じ列でH₁=δ−a+ℓ≤m−1−a、H₁≤rδを得る。ℓはactual次数1 terminalの数。
- [ ] r≥3の場合にa≥binomial(r+1,2)とH₁≤m−1−binomial(r+1,2)を接続する。r=2にはこの三角数条件やcapを課さない。
- [ ] `LowRank.Layers`へhead=H₁、tail j=Hⱼ₊₂、証明済みの有限supportを渡す。
- [ ] `NSP14.Ordinary.NumericalClosure.Data r e δ`の`rank_lo`・`embed`・`budget`・`head_linear`・条件付き`triangular_bound/head_cap`・`tail_cap`を、この一つのactual witnessから構成する。
- [ ] r≥3で既存Resourcesへの変換も利用し、過去の数値部分に仮定として残っていた資源条件がactual constructorから供給されたことを示す。

## Task 6：最大actual Q₂からApéry–Sidonへ

**Produce:** actual q₂=binomial(e,2)の下で`AperyPairData S.carrier m e`、Sidon集合、m≥e(e−1)+1とδ≥(e−1)²。

- [ ] actual非x原子の二次単項式（平方を含む）のQ₂への全射と次元の最大性から、全ての二次積の非零性・独立性を証明する。
- [ ] `AperyPairData.value : Fin e → ℕ`は0とe−1個の非x原子で構成する。個数をe−1と取り違えない。
- [ ] 0を含むpair、反復項、cross-degreeの等式も含め、`value_min`・`pair_min`・`pair_unique`をactual基底と最小生成系から証明する。
- [ ] 既存Block02の差単射・Sidon計数へ接続する。標数2、偶数/合成数mも許す。
- [ ] actual cutでr=e−1かつr≥3ならq₂最大が強制されることを証明する。r=2へこの系を延長しない。
- [ ] `NumericalClosure.Boundary r e δ`をactual witnessから供給し、rank6–8の三つの悪い角を排除する。内部点へ不要なSidon仮定を追加しない。

## Task 7：通しの検証・監査引継ぎ・Push

- [ ] 独立に進められるTask 2/6はGreenや体拡大の整備と適切に組み合わせ、同じrunで必要な接続まで進める。
- [ ] e≥3、δ=0、r=2/3、r=e−1、標数2と有限体拡大、jumpの変わる例、非零tower、tailの有限台、同じcutの同時上界を検査する。
- [ ] r=2へのmaximal-cut過大適用を防ぐため、Γ=⟨6,7,11⟩のq₂=2・r=e−1=2の境界を確認する。
- [ ] actual資源constructorとBoundaryを、既存`Data.all_rows`等へ通して数値比較まで動かす。actual Torからこの行和への上界とtarget Bettiの同定はRun15の担当として明記する。
- [ ] 全新規宣言・証明付き定義・instanceの公理依存、必要な旧Block01–13回帰、監査境界、固定依存hashを検証する。
- [ ] `verification/block14/`、監査ZIP、宣言と仮定の一覧、進捗・原稿台帳を確定し、通常commit/Push後にremote SHAとclean worktreeを確認する。

## 終了と次runへの引継ぎ

完了条件はGreen/cutの存在、offset安定化、actual towerと同一資源列、最大Q₂→Sidonが全て実証明で接続されたこと。
単に資源の条件を持つstructureを定義する、cutやGreenを未証明引数にする、数値表を再検算するだけではRun14完成としない。
今回の資源とBoundaryから既存の数値全行比較を使えることまで閉じる。

Run15へは同じsource・拡大体・P・tower・資源・同jump同型を渡す。
O_HARMONIC/O_TORのactual rank評価、算術列targetの公刊入力、actual Bettiによるordinary全体の閉鎖はRun15で証明する。
完了できない宣言は正確に列挙し、20 run計画を再校正する。予定数のために完成条件を弱めない。

本指令は先行準備した貼り付け/参照用であり、監査スレから実行スレへの直接送信は行っていない。
