# 実行スレへの指令：Run19 / V06を主経路とするN4・小生成元の閉鎖

> **For agentic workers:** Use `superpowers:executing-plans` inline. Preserve the execution thread's authorized workflow and model. This order does not request additional agents or model changes. Execute the checked tasks through validation, ledger, audit handoff and ordinary Push.

**Goal:** V06同期後の最新workを基準に、四生成元の全物理狭幅・幅4の全multiplicity・一〜三生成元を、任意体・actual完成接錐・literal interval completion・全Betti行の実証明まで閉じる。

**Architecture:** 先行するV06経路同期の証明・検証を引き継ぐ。N4ではV06本文の新cubicとactual接続を先に正確な命題として固定し、既存の二内部変数QC・元のR/Hx・三点成長・SCから必要な資源を供給する。第一行の標準語計数・小幅・幅4全m、および小生成元を接続し、Run20へ証明済みの出口を渡す。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python checker・不変証跡方式。

**Spec:** ユーザー指定の紙上固定版V06が数学的な主仕様。[先行V06同期指令の原文](../specs/2026-11-15-v06-alignment-order-input.txt)、[本指令の入力範囲](../specs/2026-11-15-run19-v06-input-scope.md)、[Run18引継ぎ](../../RUN18_HANDOFF_JA.md)を読む。V06原稿の取得・hash・該当節の確定はTask 1。V03依存表と旧Run19指令はID・既存型・旧証明との対応資料であり、V06と異なる旧経路を優先させない。

## Global Constraints

- 本書は**実行スレへ渡す事前指令**である。指令書の作成・PushはV06同期やRun19数学の実装・監査合格ではない。添付原文の「今回は実装の依頼」を、この指令作成スレでの実装命令として実行しない。
- 調査時のorigin/workは `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。Run18は六IDすべてCOMPLETE。最終R16は280 checks／268 fixtures、10662宣言／新規2421宣言。旧Run19指令の「Run18が4件未完」「R05が最新」という記載は現在の状態ではない。
- **先行同期とRun19を分ける。** Endpointの全j経路、antipodal／non-antipodal第一行の整数slack、five／sparseの共通第二行支払い、dense二枝化は先行V06同期の五項目。完了証跡を検査して再利用し、未達をRun19の成果へ付け替えない。本書はその同期を完了済みと推測しない。
- V06同期の完了・通常Pushを確認してから、Run19の実装baseを固定する。先行実行が進行中なら、そのcheckout・source・cache・HEADへ変更を加えない。独立した原典調査・契約草案までは準備できる。
- 本来の担当は次表の10 ID。小補題・途中commit・時間目安・context圧縮を終了条件にせず、actual接続、必要な修正、全検証、台帳、レビュー可能な配布物、通常Pushまで同じrunで進める。20 runは目標であり数学的条件を弱めない。
- 禁止：追加数学公理、`sorry`、`admit`、`sorryAx`、`native_decide`、未証明の解消／Tor比較を持つstructure、比較結論を引数にした閉鎖wrapper。許容推移公理は`propext`・`Classical.choice`・`Quot.sound`のみ。
- N4は `0<a<b<u`、`u≥3`、`d≥1`、`gcd(a,b,u)=gcd(m,d)=1`、**`m≥d*u+2`**。`P=P_C`、sigmaは同じ実QCの内部socle、R/Hxは元の向き。CM、`P_C=P_G`、`d=1`、`gcd(m,u)=1`、各offsetのunit性を追加しない。
- targetは物理幅`V=d*u`のliteral `S.intervalCompletion he`。source・targetはそれぞれ自身のactual最小変数と`FormalTangentAlgebra k`を使う。群のunitやラベル交換をsource全体の同型・R/Hx保存と解釈しない。
- 全jの`competitorFiber`、actual kernel、PC/PG補償を保持する。新しいN4 consumerにも停止定理を主経路へ戻さない。旧Stoppingと有限計算枝は保存する。
- V06の新cubicを古い四次／五次評価で置き換えただけで「V06同期済み」としない。旧補題は保持できるが、主consumerからV06の新補題へ至る使用経路を検査する。
- 既存sourceの編集は事前に固定した有限の許可リストに限る。基本は新NarrowFour／SmallEmbedding module・新監査・新検証器の追加。旧公開型、旧検証器、checker、frozen acceptance、全過去verification／artifactのbytesを保持する。

| 閉鎖ID | 必須の出口 |
|---|---|
| N_DISTANCE | 同じ実QCの標準語downset、三点距離和、内部socle三角形と資源上界 |
| N_WORDS | 純語・混合語長、元の向きのheight、元のRへの接続 |
| N_HIGH | V06の新cubic／actual接続を使うN4全幅の第2–4行 |
| N_FIRST | V06で採用された実標準語計数と無限範囲の第一行 |
| N_SMALL | V06の残余小幅を任意m/d/Fieldで閉鎖 |
| N_WIDTH4 | 最後の幅4族を全mで閉鎖 |
| N_CLOSE | 元の四生成元S・全物理狭幅・全行のactual completion比較 |
| I_BASE | 一・二生成元とliteralな幅0 targetを含む実比較 |
| X_LTV | 三生成元の必要なLTV契約の実証明 |
| I_THREE | 元の三生成元S・全幅・全行の実比較 |

## Review Focus

1. V06本文のcubic、適用下限、小幅例外、actual資源の同一性を保つ。純算術だけでactual接続を済ませない。
2. SCの両ラベルと整数関係を元の同次数端点表示へ戻し、実socleの全三角形・標準語の独立性を証明する。
3. 幅4は全jの競合からK',L'の両座標・制限anchor・正確な閾値を導く。有限m表やj=1の仮定で済ませない。
4. i=0、source top／消滅後、target自身のtop、u=3,d=1、V=4、e=1の幅0を省略しない。
5. V06で改変済みのEndpointと新Run19 moduleを新sourceでcold検証し、改変旧宣言も型・公理・経路監査の対象にする。

---

## Task 1：先行同期・V06原稿・10受入型を固定する

**Files:** Create `docs/RUN19_INPUT_INVENTORY_JA.md`, `docs/RUN19_V06_LEMMA_MAP_JA.md`, `docs/RUN19_CLOSURE_STATUS.json`, `audit/run19/RequestedGoals.lean`, `tests/Run19Contracts.lean`, `audit/run19/acceptance/`, `verification/run19/sources/`。

**Consumes:** 最新work、先行V06同期のsource／検証／レビュー、V06本文、Run18六閉鎖。**Produces:** 今回のbase、数学原稿の固定receipt、10 PropとV06補題対応表。以下の新module／宣言名は設計候補であり、既存exportとして扱わない。

- [ ] `git fetch origin refs/heads/work:refs/remotes/origin/work`で最新workを取得。適用AGENTS、既存作業、到着済み監査修正を確認し、base SHA・採用差分を記録する。先行実行のdirty成果を上書きしない。
- [ ] 先行同期五項目の「新補題→actual consumer→Run18凍結受入」、source/evidence/reviewのGit bytes、fresh再構築範囲、依存検査、通常Pushを確認する。`V06_ALIGNMENT_COMPLETE`という文字列だけでは受理しない。
- [ ] V06原稿を取得して実SHA・内容・該当節を記録する。共有された候補ZIP SHA256は `788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d`。実物未取得で一致を宣言しない。別版なら版差を明示する。
- [ ] **新cubicの式は添付同期指令に含まれない。** V06本文から変数、数体系、全仮定、下限、等号／不等号、全係数、例外幅、actual sourceへの橋を対応表へ転記する。式を推測して作らない。本文未取得の項目は未確定と記録し、その項目のV06一致を認定しない。独立な小生成元・原典調査は進められる。
- [ ] 旧IDとの対応は、最終actual出口を保持しつつ、V06で保持／置換／不要化された中間補題を一つずつ区別する。不要になった旧主経路を、ID数を合わせるため再実装しない。中間契約を変更する場合はV06の正確な新statementと旧statementの関係を先に明記する。
- [ ] 最終比較はe≥2で `Run18.Requested.Comparison S k he` と同じactual対象。N_CLOSEは`S.embeddingDimension=4`・物理狭幅・全i、I_THREEは`=3`・全幅・全i。N_HIGHは同じN4対象の全`2≤i`。I_BASEにはe=1のliteral carrier等式と実Betti列を含める。10 Propを通常／explicit型とhashごと凍結する。
- [ ] 要求する名前付き受入は候補 `NSP14.Run19.{distance_closed,words_closed,high_closed,first_closed,small_closed,width4_closed,narrow_four_closed,base_closed,ltv_closed,three_closed}`。最初のREDは該当宣言の不在だけで失敗することを記録。import／構文失敗をRED成功にしない。
- [ ] Run18の`RequestedGoals.lean` SHA256 `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`と六閉鎖を継承する。Run18を未完として再実装しない。V06の`PASS_WITH_EXACT_SCOPE`という紙上監査表示はLean認証の代用ではない。

**Check/Commit:** 契約定義fixtureと型検査はPASS、未実装受入は指定unknown declarationのみFAIL。V06本文の未取得を隠さず入力状態をcommitする。定義作成を数学的閉鎖と数えない。

## Task 2：実QCの二変数標準語・socle・元のheightを接続する

**Files:** Create `NSP14/NarrowFour/CoreWords.lean`, `SocleTriangle.lean`, `Distance.lean`, `StandardWords.lean`; tests `N4CoreWords.lean`, `N4Distance.lean`, `N4StandardWords.lean`。

**Consumes:** `TwoMonomial.two_internal_kernel_ideal`, `internalPoint_injective_two`, `InternalSocleBasis.internalSigma_point_count`, `threePoint_coprime_growth`, `wordVolume_tail`, `savchevChen_twoValue`, `normalized_modular_relation`。元のtwoInternalEquivの任意ラベル付けと、a<bの順序を混同しない。

- [ ] 実内部offsetの順序付き二要素をy,zへ対応付ける。実CoreMinimalIndexと有限downsetの全単射、Pのcardinality、作用の生存／消滅を証明する。既存のkernel単項式性・単射を再利用し、別modelだけの計数にしない。
- [ ] 実共通annihilatorとdownset極大点の対応を供給する。極大点を順序付け、全次数sigma−1の語と約数が標準になることを証明し、`C(sigma+1,2)≤P`へ接続する。
- [ ] 三点成長から同じDの距離尾和を評価する。V06でも保持される `W≤1+floor(u²/4)`等は実wordVolumeへの等式を介して証明する。合成数u・非自明stabilizer・非unit offsetを排除しない。
- [ ] 標準語の純軸上限と、混合語長の`2*(s+t)≤u`をSCから証明する。SCの両ラベル交換を処理し、元の整数offset間の同次数関係、全指数の非負性、端点因子があることから矛盾を得る。
- [ ] 元の座標のheightを実CoreMinimalから評価し、元のRの上界へつなぐ。`actual_two_row_one/two/three/four`はactualR版、`actual_two_all_rows`はRhat版なので、同じ名前の資源として混ぜない。
- [ ] collective gcdのみが1の例、階段downset、sigma=1、SC交換の両側、混合長の床境界、u=3/4のR=0を名前付き受入で検査する。Q/F2/F3の実QCにも適用する。

**Check/Commit:** 新module build、三fixture、N_DISTANCE/N_WORDSの凍結受入をGREENにする。先行同期後の`SocleBounds`等の経路がStoppingへ戻っていないことも確認する。

## Task 3：V06の新cubicからactual第2–4行を閉じる

**Files:** Create `NSP14/NarrowFour/CubicPayment.lean`, `HigherRows.lean`; tests `N4CubicPayment.lean`, `N4Higher.lean`。

**Consumes:** Task 1で凍結したV06の正確なcubic／下限／例外とTask 2の同じ資源。既存入口は`actual_two_row_two/three/four`、`actual_positive_rows_add`、先行V06同期の共通higher API、実target lower profile。

- [ ] V06対応表の純算術命題を先にRED受入へ写し、正確な係数恒等式と非負性をLeanで証明する。符号付き差はInt/ℚで扱い、Nat飽和減算を負の多項式の代用にしない。
- [ ] 同じP・sigma・元のRまたは正当化済みRhatを代入して、V06のcubicをactual β₂へ接続する。新cubicとactual接続は二つとも必要である。
- [ ] V06が共通higher APIを用いる場合、**actual β₂≤target₂だけを仮定にせず、同じBの第二行資源支払い**を供給する。Bがℚでも使える型、正のchoose分母、i=eの別扱いを保持する。V06の実際の導出が別ならその正確な橋を対応表に従って実装する。
- [ ] 第3・4行、source消滅後の行、例外幅を原稿の範囲どおり接続する。旧Run19の四次／五次多項式や行別比較を主経路へ呼び戻しただけで本Taskを完了にしない。
- [ ] u=3,d=1はAP/carrier APIからsource=targetを供給する（既存`narrow_fullAP_comparison`のhe≥5をe=4へ誤適用しない）。V=4で、V≥5が必要なtarget下界を使わない。V06のcubic適用下限とその直前、i=2/3/4/5、m=d*u+2、d=1/3、Q/F2/F3を検査する。

**Check/Commit:** build・両fixture・N_HIGH受入をGREENにし、新cubic→実資源→actual行→literal targetの経路を保存する。算術単独のGREENでは閉鎖としない。

## Task 4：V06の第一行計数と残る小幅を閉じる

**Files:** Create `NSP14/NarrowFour/Relations.lean`, `FirstCount.lean`, `FirstLarge.lean`, `SmallWidths.lean`; tests `N4First.lean`, `N4Small.lean`。

**Consumes:** Task 1のV06該当節、Task 2、同じactual第一行。旧N4置換稿の式は、V06でも採用されていることを確かめたものだけ使う。

- [ ] V06で使う禁止語を、元の実coreの同次数・同offset関係から証明する。保持される三関係は `y^b=x^(b−a)z^a`、`z^(u−a)=y^(u−b)v^(b−a)`、`y^(u−b)z^a=x^(u−b)v^a`。右辺の端点因子と指数範囲を示す。
- [ ] 純軸の単位元を一度だけ数え、混合三角形／禁止矩形の有限集合写像からPとsigmaを評価する。旧式 `E_h(k0)=C(h−k0+2,2)` を使うなら`k0≤h`のguardを保持する。V06が別計数ならその正確な集合と対応を証明する。
- [ ] 元のR/Hxとactual第一行へ接続し、V06の無限範囲を全称定理で払う。幅6–8など原稿に残る小幅は、明示的な関係とdownset包含により任意m/dで閉じる。
- [ ] 旧196組証書、有限m探索、反射後のR、core計算の最大値を証明前提にしない。V06で不要になった小幅分岐を旧計画に合わせて復活させない。
- [ ] V06の各境界と例外offsetを名前付き定理にし、元の向きのR>0、非unitケース、u=3/4/5/6/7/8/9/10、k0のguard境界、Q/F2/F3を必要範囲で検査する。u=4の通常二対で`P+sigma≤5`が必要なら、別々の粗い上界の単なる加算で済ませない。

**Check/Commit:** N_FIRST/N_SMALLの元の最終出口と、V06で必要な中間契約をGREENにする。V06本文と旧稿の適用範囲差を対応表へ明記する。

## Task 5：幅4の最後の族を全mで閉じる

**Files:** Create `NSP14/NarrowFour/WidthFourCore.lean`, `WidthFourCompetitors.lean`, `WidthFourInitial.lean`, `WidthFourComparison.lean`; test `N4WidthFour.lean`。

**Consumes:** V06で保持される幅4証明、actual全競合核。対象は`d=1,u=4,a=1,b=3,m≥6`。以下は既存V02 §14.6の実式であり、Task 1でV06の採用箇所との一致を確認して使う。

- [ ] 内部重みwt(y)=1, wt(z)=2, wt(x)=wt(v)=0、通常次数、固定lexの順に比較する実well-founded順序を作る。`J0=(y³,yz,xz²,z³)`の標準列1,y,y²,zとx-free列z²の実像の独立性・停止除算を証明する。
- [ ] 列基点の次数／offsetを(c,n)とする。任意j≥1について `r_j=(n−jm) mod4`、`kappa_j=(jm+r_j−n)/4`、lambda=(0,1,2,1)、`Delta_j=lambda(r_j)−c−kappa_j−j`をIntで定義し、**K'=K−kappa_j, L'=L−Delta_j**と両非負条件のiffを供給する。
- [ ] `4Delta_j<0`、制限anchorの`K≥kappa_j+1`が自由anchorに包含されること、kappa_jの単調性を全jで証明し、j=1が正確な閾値であると導く。先にj=1へ核を切り詰めない。
- [ ] `theta_n=max(ceil((m−n)/4),0)`は整数差を取ってから切上げる。追加禁止語のactual消滅と非禁止語の最大分解長・同次数weightの独立性を証明して、actual `in(I_G)=J0+(b*v^theta_n)`を得る。
- [ ] 最小生成元の先頭項から実同次生成元を持ち上げ、実defining idealとactual Torへの橋を通してβ₁≤mu(J)を証明する。
- [ ] m=6は上界6／実target9。m>6は四剰余で上界6/8/8/6、実target7/10/9/8を**全Q**で証明する。m=7/8/9/10、任意Q、char2/3、thetaの正値／0境界を検査する。

**Check/Commit:** build・fixture・N_WIDTH4受入GREEN。候補生成元数やHilbert表だけでinitial ideal等号を宣言しない。

## Task 6：元の四生成元Sの全物理狭幅・全行へ合成する

**Files:** Create `NSP14/NarrowFour/Comparison.lean`, `audit/run19/ClosedN4Goals.lean`; test `N4ActualClosure.lean`。

- [ ] 元のSのe=4からendpointDataのq=2、u≥3、V=d*u、実sourceとのBetti同一性を供給する。
- [ ] V06の分割で第一行の全uを覆い、第2–4行はTask 3、i=0は双方1、i>4はsource=0とtarget非負で閉じる。target自身の高い行をsource topで消さない。
- [ ] N4七IDと`narrow_four_closed`を凍結型で証明する。consumerの追加前提に未証明の資源／比較を入れない。
- [ ] m=d*u+2、d=1/3、分岐の両側、R>0/P_C≠P_Gの非CM source、source/targetの変数数が異なる例、i=0/4/5とtarget自身のtopをQ/F2/F3で適用する。
- [ ] 新N4主consumerのimport／使用定理閉包にStoppingを戻していないことを検査する。幅4の全jからの局所還元と、一般核を停止計算へ戻すことを区別する。

**Check/Commit:** N4七受入GREEN。Run19の残る三IDも続け、N4完成だけで本runを終了しない。

## Task 7：一・二生成元と幅0のliteral targetを閉じる

**Files:** Create `NSP14/SmallEmbedding/Base.lean`, `NSP14/Semigroup/IntervalCompletionAll.lean`; test `SmallEmbeddingBase.lean`。

- [ ] 全S用completionを追加するなら、carrierが無条件に`AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom)`であること、he≥2で既存completionと一致することを証明する。旧APIは保持する。
- [ ] e=1では唯一の原子が1、S=N、m=maxAtom=1を証明し、literalな[1,1]の閉包と実Betti列(1,0,0,...)を供給する。targetを便宜的にSと定義しただけで済ませない。
- [ ] e=2では実atoms m<nとgcd(m,n)=1を抽出し、実接錐を`k[X,Y]/(Y^m)`へ同定。完備化の橋と実Koszul/Torから(1,1,0,...)、実targetの第一行≥1を証明する。
- [ ] S=N、<2,3>、<3,5>、幅0、source消滅後とtarget top、任意FieldおよびQ/F2/F3を検査し、`base_closed`をGREENにする。

## Task 8：LTVの実証明と三生成元の全域consumerを閉じる

**Files:** Create `NSP14/SmallEmbedding/ThreePresentation.lean`, `LanTuVu.lean`, `ThreeComparison.lean`; tests `LTVActual.lean`, `SmallEmbeddingThree.lean`; provenance `verification/run19/sources/`。

- [ ] [Lan–Tu–Vu arXiv:2307.05589v1 Theorem1.1](https://arxiv.org/html/2307.05589v1#S1)の本文・参照証明とV06の引用範囲を読む。必要な契約が理想／商、graded／total、どのtarget、どの標数かを記録する。
- [ ] 固定ライブラリと既存exportを実型まで調べ、必要な三生成元のdefining ideal・initial ideal・解消または実Tor比較を証明する。再利用sourceはURL/commit/license/hash/適応差分を保存する。
- [ ] 理想のBettiから商の正行へは一段shiftし、i=0を補う。元のactual完成接錐・literal completion・双方の最小変数へ運び、任意体の全iを閉じる。
- [ ] CM/非CM、幅m−2/m−1の両側、i=0/1/2/3/4、Q/F2/F3の実sourceで検査し、`ltv_closed`と`three_closed`をGREENにする。ordinaryだけのconsumerを全三生成元と数えない。

## Task 9：V06同期後のbaseを継承する全検証・認証・通常Push

**Files:** Create `scripts/verify_run19.py`, `scripts/check_run19_n4.py`, `scripts/check_run19_guards.py`, `scripts/package_run19_audit.py`, `docs/RUN19_EXECUTION_LEDGER_JA.md`, `docs/RUN19_PAPER_CORRESPONDENCE_JA.md`, `docs/RUN19_FINAL_REVIEW_JA.md`, `docs/RUN19_HANDOFF_JA.md`, `audit/run19/ClosedGoals.lean`, unique `verification/run19/runs/` and new archive。

- [ ] **旧`verify_run18.py`を緩めない。** V06同期は旧BASEより前からあるEndpointを改変するため、旧「既存source不変」検証を現HEADへ直接再適用しない。先行`verify_v06_alignment.py`等の変更管理と証拠を検査し、Run19用に採用base SHA・新設ファイル範囲・有限変更許可リストを固定する。
- [ ] 実行時最新の成功V06同期証跡の**全実質check／全fixture／新しい経路検査**と、Run18 R16の268 fixtures／280 checksの実質被覆を継承する。増えた検査を落とさず、old-command→new-commandの対応表を保存する。旧280コマンド文字列をそのまま実行しない。
- [ ] `--output`／`--output-dir`／EnvironmentAudit／旧checker固定先を、新しい排他的directoryまたは使い捨てrootへ写像する。Run18公理controlのprefix制約により新Run19用adapterが必要なら新設し、旧scriptや旧出力先を改変しない。新scriptが作る添付証拠先も全て記録する。
- [ ] rootと新規moduleが`lake build NSP14`から到達するようimportを追加する。root・進捗・対応表は旧prefixを保持して追記。source freeze前に、全対象Lean、全使用checker（継承scriptも含む）、新verifier/packager/guard、変更規則、V06原稿receipt、凍結契約、対応台帳、固定依存をmanifestへ収録する。
- [ ] V06で変わった既存Endpointと全下流、今回の新規／変更productionのlib/IR、root、test/auditをfreshにして再構築範囲を保存する。mathlib全体をcoldにしたとは表示しない。全fixtureを依存順に実行し、各processの終了コード・警告・生ログを保存する。必要なら`-j1 -M12288`を使う。
- [ ] 全新規および継承した改変旧moduleの宣言・instance・helperを実環境から抽出し、normal/explicit型・module/source hash・`collectAxioms`・自己依存を監査する。baseの公開型と比較し、`axiomInfo`表示だけで追加公理と誤判定しない。未importの新fixtureをcoverageに数えない。
- [ ] 許容公理と主証明経路は別に検査する。先行V06の根別依存条件を維持し、新N4で実際に新cubicが使われることを確認する。umbrella NSP14の旧成果importを根別不採用判定に使わない。旧有限計算枝は回帰する。
- [ ] 新verifier自身のnegative controlsを分離環境で検査する。少なくとも危険／既存出力先、許可外source改変、source/evidence差替え、改変旧moduleの型／公理coverage欠落、継承fixture／V06経路検査の脱落、review不一致、既存ZIP上書きを拒否する。旧guardsのPASSだけを新認証の検査にしない。
- [ ] 独立checkerでV06 cubicの全係数と境界、三角／矩形計数、小幅、幅4四剰余をexact算術で検算し、actual core/Gの標数0/2/3を別計算する。有限一致を一般証明や標数間rank一致の仮定にしない。
- [ ] proof commitを固定し、HEADとbound sourceを凍結して検証する。旧全verification/artifactと失敗履歴はbytes/filesetを保持し、新規先だけへ出力する。検証中・レビュー中のsource変更は新snapshot／新証跡で再検証する。
- [ ] 10 IDの成否、V06本文→Lean補題→actual consumer→凍結出口、新cubicの使用経路、先行五項目の維持を台帳にする。Run18 COMPLETE、V06_ALIGNMENT_COMPLETE、RUN19_COMPLETE、全P14完成を別の判定として扱う。
- [ ] source/evidence/reviewを実Git bytesとSHAで束縛し、検証器・経路検査も独立レビューのscopeにする。判定が参照する**レビュー本文そのもの**をZIPへ収録し、全entry/hash/CRC・出力上書き拒否を確認する。bundleを独立実行可能な完全checkoutと呼ぶなら、その実ファイル被覆まで供給する。
- [ ] 全10 IDの元の出口とV06主経路の接続が揃う場合だけ`RUN19_COMPLETE`。途中checkpointは真の未完型・必要入力・理由を保存し、独立に進められる残タスクを続ける。旧証跡へCOMPLETEを後付けしない。
- [ ] 最新workと到着監査を再取得し、並行変更を保持・統合する。通常commit/Push後、実remote SHA・clean worktreeを確認する。force Pushせず、先行同期や監査branchを勝手に上書きしない。

**Acceptance:** 新しい`verify_run19.py --fresh-test-cache --output-dir verification/run19/runs/<new-id>`が全実質checkをPASSし、10凍結受入・V06経路検査・型／公理検査がGREEN。レビュー対象と公開bytesが一致し、通常Pushとremote/cleanを実測する。

## Run20への引継ぎと最終報告

- [ ] 任意体・元のSの`narrow_four_closed`、`base_closed`、`three_closed`と、全Sで定義できるliteral target／既存target一致を渡す。Run18の`narrow_width_comparison`とordinaryの既存出口も、先行V06同期後のsourceで再検証されたものを一覧にする。
- [ ] Run20の担当は全域分割・actual主定理合成と全体照合。通常基点の一般恒等式など別の追加依頼を無断でRun19必須へ広げず、I_PARTITION/I_MAINを本runで仮定して閉鎖しない。
- [ ] 最後に、採用base／V06 hash、10 IDの型・成否、実export、新cubic→actual接続、先行五項目の維持、fresh検証と生ログ、許容公理、proof/evidence/review/packageのbinding、ZIP、実Push SHAと残務を報告する。

**終了条件：V06に沿うN4の資源・新cubic・actual接続・第一行・小幅・幅4全mと、一〜三生成元の全行が、追加の未証明比較前提なしで元のactual sourceからliteral completionへ接続し、全検証・台帳・公開確認まで揃うこと。**

この文書の作成時点ではV06のN4本文は未提供・未取得であり、式を代作していない。原稿receiptとTask 1の命題対応が揃った後に、その部分の実装仕様が確定する。先行V06同期の実装やRun19の実装を、この指令作成スレから開始・送信していない。
