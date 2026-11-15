# 実行スレへの指令：Run20 / V06の全域分割・actual P14主定理・最終認証

> **For agentic workers:** Use `superpowers:executing-plans` inline. Preserve the execution thread's authorized workflow and model. This order does not request extra implementer agents or model changes. Continue through implementation, fixes, whole-project validation, ledger, reviewable release and ordinary Push.

**Goal:** V06のI_PARTITION・I_MAINを、全数値半群S・任意体k・全Betti行iについて、元のactual完成接錐とliteral interval completionの比較として証明し、必要入力の未証明ゼロ・全検証・原稿対応・配布物・通常Pushまで完成する。

**Architecture:** Run19とV06同期の実証明・認証を最新workから確認して採用baseを固定する。e=1/2/3を先に、e≥4を整数幅のordinary／narrowへ分け、narrowをe=4／e≥5へ分ける。既存の独立した最小表示と共通targetの同一性を保って枝を合成し、全環境・最小公開入口・V06主経路を別々に検証する。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python checker、source/evidence/reviewのGit bytesとSHA256による束縛。

**Spec:** [V06全体本文](../../../proof_sharp_v6/NS_P14_SHARP_PROOF_JA.md)、[第6章§6.1–6.3](../../../proof_sharp_v6/chapters/06_SYNTHESIS_JA.md)、[共通章BRIDGE/CAP/MINCAP](../../../proof_sharp_v6/chapters/01_COMMON_JA.md)、[V06依存・被覆](../../../proof_sharp_v6/DEPENDENCY_AND_COVERAGE_JA.md)、[Run19新版指令](2026-11-15-run19-v06-n4-small-closure-order.md)、[本指令の入力・設計範囲](../specs/2026-11-15-run20-v06-main-input-scope.md)。旧50 IDは[依存表](../../../proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)と[registry](../../../proof_structure_v3/lemma_registry.json)から対応付け、V06と異なる旧経路を主依存へ戻さない。

## Global Constraints

- **本書はRun20の事前指令であり、作成・Pushを実装やP14完成と数えない。** 先行Run19を実行中ならそのcheckout・HEAD・source・cacheへ書き込まない。最新work・到着済み監査修正を着手時に取得する。
- 調査時の最新workは `04906ede0e9e3a04b9c07c791c1e1c49834dd3e1`。Run18六IDはCOMPLETE。V06同期の公開認証は存在するが、公開treeにRun19本番module・凍結受入・完了証跡はまだ確認できない。**Run19完了を推測して合成しない。** 実行時に増えた成果を実型・証跡まで確認する。
- V06同期の認証proofは `d446fc2f18f7a8603d1eedd446e93810dc44d01c`、証跡は `verification/run18/runs/v06_alignment_20261115T152000Z_r01/verification.json`（289 checks／273 fixtures、10713宣言）。work統合は数学sourceを保つ別scopeの記録であり、証明snapshotと最新HEADを混同しない。
- 担当閉鎖IDは **I_PARTITION / I_MAIN**。Run19のN4・小生成元・LTVを未証明の前提やfieldにして閉鎖しない。到着した修正や接続不備は修理して検証する。本当の不足があればexact型・根拠・必要作業を記録し、進められる独立タスクは継続する。
- 最終主定理の前提は **S : NumericalSemigroup、k : Type、[Field k]、i : Natだけ**。e≥2、狭幅、CM、d=1、R=0、P_C=P_G、無限体、特定標数、枝の結論を仮定に残さない。一般GをArtinや有限次元k加群と仮定しない。
- targetは常に `AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom)` をcarrierとする実数値半群。全S用APIとhe≥2の既存`intervalCompletion`との対応を実証明する。source・targetそれぞれの`AtomExponent`と`FullPolynomialRing`を使う。
- e=1はS=N、m=maxAtom=1、幅0、literal [1,1]の閉包。offsetの空gcd・幅0の剰余式・he≥2の旧APIを無理に適用しない。便宜的な別targetで全S型を作らない。
- 同じcarrierでもconductor witnessは異なり得る。carrier等式だけからNumericalSemigroupの構造全体を同一視せず、`carrier_totalBetti`・`completed_totalBetti`等で実表示・actual Bettiを運ぶ。
- 禁止：追加数学公理、`sorry`、`admit`、`sorryAx`、`native_decide`、未証明の比較／解消を持つ証明書、主比較を引数にしたwrapper。許容推移公理は`propext`・`Classical.choice`・`Quot.sound`のみ。
- 固定依存、既存公開型、凍結受入、原稿・過去verification/artifactのbytesを保持する。既存source編集は事前に有限許可リストへ固定し、理由・型保存・再検証を記録する。旧verifierのBASE不変ガードを緩めない。
- 20 runは運用目標であり、成立の保証・未完を隠す理由ではない。小補題・内部commit・30〜60分・context圧縮を終了条件にせず、数学の閉鎖から公開確認まで同じrunで進める。

## Review Focus

1. 主定理が**全S・任意体・全i**で、双方のactual最小表示とliteral targetを保つか。e=1を別の無関係な系へ落としていないか。
2. 整数幅の境界`w=m−1`がordinary、`w=m−2`がnarrowに入り、e=4/5、全cut rank、δ=0、物理下限m=du+2を覆うか。
3. i=0、i=e、i>e、target自身の上端を区別するか。source消滅後もtargetが非零になる例で検査する。
4. Run19・LTV・全S target・ordinaryの有限体下降が真の実証明か。status、名前、紙上引用、有限checkerだけから完成を推定していないか。
5. 最新sourceで全fixture・全宣言・改変旧型・V06経路を再検証し、旧証跡・review・配布Git bindingを保持するか。新しい主定理へ古い証跡を後付けしていないか。

---

## Task 1：最終統合に使う実入力を確定する

**Files:** Create `docs/RUN20_INPUT_INVENTORY_JA.md`, `docs/RUN20_CHANGE_POLICY.json`, `docs/RUN20_CLOSURE_STATUS.json`, `docs/RUN20_DEPENDENCY_COVERAGE.json`。未完は `docs/RUN20_UNPROVED_DECLARATIONS.md`へ正確な型で記録する。

**Consumes:** 最新work、Run19 handoff/凍結型/成功証跡/レビュー、V06同期handoff/統合記録、Run15–18閉鎖。**Produces:** 採用base SHA、有限変更規則、実exportと入力証跡一覧。

- [ ] `git fetch origin refs/heads/work:refs/remotes/origin/work`を行い、AGENTS・dirty成果・到着監査修正・公開履歴を確認する。先行実行の作業を上書きせず、適切な隔離場所を使う。
- [ ] Run19の10 ID、actual N4の新cubic→行比較、全mの幅4、I_BASE/X_LTV/I_THREE、全S targetが凍結型のまま閉じたことを実source・通常/explicit型・最新cold検証・reviewの対応まで確認する。最新公開に存在しない候補名を既存exportと表示しない。
- [ ] Run19の未完が残っていれば、このrunで仮定して隠さない。exact型と未完箇所を引き継ぎ、独立な分割・target transport・検証器・台帳の準備を進める。統合に必要な修理は記録して実証明し、数学的に未達ならMAINをCOMPLETEにしない。
- [ ] 既存入口 `Ordinary.ordinary_actual_completion_betti_le`、`NumericalSemigroup.narrow_width_comparison`、Run19の`narrow_four_closed`相当、`base_closed`相当、`three_closed`相当を同じS/k/iへ適用できる型として登録する。auditの閉鎖名だけでなくproductionの証明へ到達する経路を記録する。
- [ ] V06同期のproof/evidence/reviewと、`v06_alignment_integration_20261116_r01/receipt.json`等のcode-identical統合scopeを確認する。記録された289/273を最低被覆の参考とし、Run19で増えた実質checkを全て継承する。
- [ ] 原稿の全体SHA `fe8271bbaabf6b3d31243628c3a5a5a305b82361c794f03c6e13a2fe98c72791`、第6章SHA `67a10b00ab51ab1836fc071bb1c03b9fa2898ec470e84762151aeba032316f4d`を照合する。別版を使うなら版差と採用理由を明記する。
- [ ] 既存全ファイル・source型・過去証跡のbaselineを固定する。編集許可はMain接続に必要な有限リスト、新規Main module・監査・検証器・tests・docsへ限定する。rootと二つの既存台帳は旧prefixを保存して追記する。

**Acceptance:** 入力一覧の「証明済み／未完／紙上のみ／歴史的証跡」が実在と一致する。Run19やV06同期のstatus文字列だけを根拠にしない。以後の新名は候補であり、Task 2で実APIへ合わせて固定する。

## Task 2：literalな全S targetと最終受入型を凍結する

**Files:** Create `NSP14/Main/IntervalTarget.lean`, `audit/run20/RequestedGoals.lean`, `tests/Run20Contracts.lean`, `audit/run20/PartitionClosed.lean`, `audit/run20/ClosedGoals.lean`, `audit/run20/acceptance/I_PARTITION.lean`, `audit/run20/acceptance/I_MAIN.lean`。

**Consumes:** Run19の全S用target、既存`intervalCompletion_carrier`、`CarrierTransport`、`ActualTorTransport`。**Produces:** 公開主定理が使う一つのtarget、I_PARTITION/I_MAINの凍結型とhash。

- [ ] Run19が供給した全S APIを再利用する。候補名は`S.intervalCompletionAll`。別名なら正確な既存名へ下記型を置き換え、その対応を凍結時に記録する。未実装ならRun19 I_BASEの不足として実証明し、targetを単なるSや数値profileで置き換えない。
- [ ] 無条件のcarrier等式、he≥2で旧intervalCompletionとのcarrier一致、e=1でliteral [1,1]の閉包、source/targetの実最小変数のtransportを供給する。構造のconductorが異なる場合は`carrier_totalBetti`と両側の`completed_totalBetti`で完成接錐の行を同定する。
- [ ] 下記のI_MAINをPropとして定義し、通常/explicit型・展開後のsource/target環・hashを保存する。全行を`i≤e`へ縮めず、e≥2や枝の結論をsection変数に残さない。

```lean
-- intervalCompletionAllはRun19の実APIに合わせて確定する。
def I_MAIN : Prop :=
  ∀ (S : NSP14.NumericalSemigroup) (k : Type) [Field k] (i : ℕ),
    let T := S.intervalCompletionAll
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    NSP14.Homological.totalBetti k T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i
```

- [ ] I_PARTITIONはTask 3の六領域の全被覆・排他性、ordinaryのcut三領域とその適用条件、narrowの正規化範囲を含めて凍結する。主定理の比較そのものを分割の入力に入れない。
- [ ] 二つの閉鎖auditファイルは最初に凍結契約をimportするだけの骨組みを作る。`NSP14.Run20.partition_closed`、`NSP14.Run20.main_closed`を要求する名前付き受入を先に実行し、該当宣言不在だけのREDを保存する。依存import・構文失敗をRED成功に数えない。骨組みにaxiom・sorry・仮の証明を置かない。
- [ ] `Run20Contracts`は契約定義・全S target・旧API整合の検査としてPASSさせる。定義作成や型の表示を実証明の閉鎖と数えない。

## Task 3：全パラメータの排他的分割を証明する（I_PARTITION）

**Files:** Create `NSP14/Main/Partition.lean`; modify `audit/run20/PartitionClosed.lean`; test `tests/MainPartition.lean`。

**Consumes:** `S.embeddingDimension_pos`、`S.multiplicity_pos`、`embeddingDimension_le_multiplicity`、`actualCutRank_two_le/le/triangular`、`degree_two_le_deficit`、`WidthNormalization`。**Produces:** `NSP14.NumericalSemigroup.parameter_partition`等の実分割と`partition_closed`。

| 大分岐 | 正確な条件 | 合成する出口 |
|---|---|---|
| 一生成元 | e=1 | Run19 I_BASEのliteral target比較 |
| 二生成元 | e=2 | Run19 I_BASE |
| 三生成元 | e=3 | Run19 I_THREE（LTV実証明） |
| ordinary | e≥4, m−1≤w | ordinary_actual_completion_betti_le |
| 四生成元narrow | e=4, w≤m−2 | Run19 N_CLOSE |
| 五生成元以上narrow | e≥5, w≤m−2 | narrow_width_comparison |

- [ ] e≥1から小生成元三枝とe≥4を覆い、e≥4ではm≥4を確保して、Nat減算でも`w≤m−2`と`m−1≤w`が排他的かつ全域であることを証明する。`w=m−1`をnarrowへ入れない。
- [ ] ordinaryの実r=`S.actualCutRank`について `2≤r≤e−1`、`r=2 ∨ r=3 ∨ 4≤r≤8 ∨ 9≤r`、`9≤r→10≤e`、`3≤r→C(r+1,2)≤δ`を既存実データから供給する。δ=0ではr=2を導き、空塔を排除しない。
- [ ] narrowでは同じ元のSの`endpointData`からq=e−2、u≥q+1、d≥1、V=d*u=w、m≥V+2、元のgcd条件を供給する。e=4のu≥3、e=5のu≥4、e≥6のedge/dense/sparse範囲が穴なく覆われることを示す。
- [ ] 既存の各branch閉鎖証明をこの分割へ戻して循環させない。幅4の全m証明やdense数値支払いを再実装する必要はない。
- [ ] m−2/m−1の境界、e=1/2/3/4/5/6、cut r=2/3/4/8/9、δ=0、u=e−1/e/2e−3/2e−2を名前付き受入にする。数値例だけでなく全Sの分割定理を実際に適用する。

**Check/Commit:** `lake build NSP14.Main.Partition`、MainPartition、凍結I_PARTITION受入がGREEN。有限分割checkerを全称証明の代用にしない。

## Task 4：各枝を同じtarget・元の体・完備接錐へ合わせる

**Files:** Create `NSP14/Main/Branches.lean`; tests `tests/MainTargetTransport.lean`, `MainBranchConsumers.lean`。

- [ ] 小生成元、ordinary、N4、五生成元以上narrowの各production exportを、その元の適用条件だけで同じ全S targetへ運ぶ。各branch consumerは比較結論を追加引数に取らない。
- [ ] ordinaryは`NSP14.Ordinary.ordinary_actual_completion_betti_le`をe≥4へ適用し、既存targetとのcarrier/Betti一致だけを使って全S targetへ接続する。一般の`ordinary_betti_bound`の数値上界だけでactual target比較を省略しない。
- [ ] ordinary内の体拡大から元のkへの下降が`actualG_totalBetti_baseChange`で実証明済みであることを読み取り確認する。最終定理にInfinite/CharZero仮定、別体のsource、体拡大済みのtargetを残さない。
- [ ] narrowのe=4はRun19 N_CLOSE、e≥5はRun18/V06後の`narrow_width_comparison`を使い、V=d*uを保つ。e≥5定理へe=4を通したり、u幅の仮想targetに置換したりしない。
- [ ] e=1/2/3を全幅で接続する。e=3のordinaryだけでLTV全幅を代用しない。理想/商の添字shiftはRun19の実証明を再利用する。
- [ ] 同じcarrierでconductor witnessだけ異なる二つのSを作り、完成接錐のBetti transportを検査する。source/targetの最小変数が異なる実例でtarget同定を検査する。

**Check/Commit:** 各branchの任意S/k/i consumerと二fixtureがGREEN。主定理を仮定にした循環やconditional certificateのconsumerを閉鎖として数えない。

## Task 5：公開主定理を合成する（I_MAIN）

**Files:** Create `NSP14/Main.lean`; modify `audit/run20/ClosedGoals.lean`; test `tests/MainPublicAPI.lean`。Modify `NSP14.lean` by appending public import only。

- [ ] 公開候補名 `NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion`を、Task 2のI_MAINと同じ全称型で証明する。Task 3の分割とTask 4の実consumerを合成し、追加の数学的前提を受け取らない。
- [ ] 全行の枝定理をそのまま合成できる場合は再度行別に分ける必要はない。別途処理する場合、i=0は両側1、1≤i≤eはi=eを含め各枝、i>eはsource=0とtarget非負で閉じる。targetがsourceと同じ上端で消えるとは主張しない。
- [ ] `ClosedGoals`でTask 3の`PartitionClosed`をimportし、`NSP14.Run20.main_closed : Requested.I_MAIN`と二担当IDの`all_closed`を証明する。production Mainは実productionの枝証明を使い、audit-onlyのwrapperやfixtureを主証明へimportしない。
- [ ] 主定理の型は元Sと元k、双方のFormalTangentAlgebra、各AtomExponent、全iであることをnormal/explicit出力で保存する。he≥2の旧targetを使う互換系も提供するが、それだけを全S主定理と表示しない。
- [ ] `tests/MainPublicAPI.lean`は`NSP14.Main`と必要な体の標準importだけで主定理を使用する。umbrellaやauditを先に読まないと公開APIが使えない状態を残さない。

**Check/Commit:** `lake build NSP14`、MainPublicAPI、I_MAIN/I_PARTITIONの元の凍結受入が全GREEN。主定理名やCOMPLETEフラグの存在だけで成功を判断しない。

## Task 6：主定理を通る実境界fixtureと独立検算

**Files:** Create `tests/MainActualExamples.lean`, `tests/MainBoundaryRows.lean`, `scripts/check_run20_partition.py`。

- [ ] 全例で新しい公開主定理を呼ぶ。旧branch定理を直接呼ぶだけのfixtureを、新しい合成経路の検査として数えない。任意Field版とQ/ZMod2/ZMod3を用意する。
- [ ] S=N、二生成元<2,3>/<3,5>、三生成元<4,5,6>（w=m−2）/<4,5,7>（w=m−1）を実最小原子とともに確認する。S=Nは幅0のliteral targetを使う。
- [ ] 四生成元<6,7,9,10>（narrow境界・幅4最終族）と<6,7,9,11>（ordinary境界）を使い、e=4での分岐の両側を検査する。有限m列挙を全m証明にしない。
- [ ] 後者はsourceのe=4を超えるi=5でsource=0、targetはordinary半群<6,7,8,9,10,11>で **β5=5**。この実値を既存AP公式から名前付き定理として確認し、source消滅からtarget消滅を推論する誤りを検出する。
- [ ] Run18/19の物理最小m=d*u+2、d>1、非CM・R>0/P_C≠P_G、e=5小幅/antipodal nonunit、e≥6 edge/dense/sparseの実fixtureを再利用し、主定理で比較する。dense q=4,t=3の等号境界、幅4の四剰余とm=6を保持する。
- [ ] i=0、source e、e+1、target自身のembeddingDimensionを検査する。ordinaryのδ=0/空塔、低cutとr≥9への既存fixtureも継承し、数値パラメータを実現するSの存在を無証明で仮定しない。
- [ ] 独立checkerは整数分割・target profile・fixtureパラメータをexact算術で検算する。共通actorial分母の符号、Nat減算、V=uでない例、target最小表示のv=min(w,m−1)を確認し、有限検算を主定理の全称性に置換しない。

**Check/Commit:** 新規全fixtureがGREEN、独立checkerが一意な新規出力先でPASS。紙上数値とactual変数数をともに記録する。

## Task 7：V06・旧50 ID・実依存と原稿を最終照合する

**Files:** Create `docs/RUN20_PAPER_CORRESPONDENCE_JA.md`, `docs/RUN20_EXECUTION_LEDGER_JA.md`, `docs/RUN20_HANDOFF_JA.md`。Update Task 1の`docs/RUN20_DEPENDENCY_COVERAGE.json`／`docs/RUN20_UNPROVED_DECLARATIONS.md`。Append `LEAN_PROGRESS.md` and `docs/LEAN_PAPER_ALIGNMENT_JA.md` only。

- [ ] 旧registryの50 IDそれぞれを実export／証明群／元の型・量化／actual consumer／V06節へ対応付ける。集約X_BASIC等は必要な有限性・Tor・Gröbnerの実補題群を列挙する。名前付きwrapper数を50まで増やすことを目標にしない。
- [ ] V06で不要化された強い中間結果は、主依存から外した理由と、独立の旧結果として保持する範囲を記録する。不要化を「旧命題がLeanで証明された」と言い換えない。過去の構造checkerのPASSやrun番号を閉鎖証明にしない。
- [ ] 全7公刊入力の必要な契約は、元の量化・任意標数性・実Tor/actual consumerまで追う。特にX_LTVを引用名のaxiomや未証明のresolution証明書で代用していないことを確認する。
- [ ] V06第6章の全域、共通章BRIDGE/CAP、N4新cubic、先行五項目の新経路を確認する。一般端点の全j kernelと元のR/Hx、PC/PG補償、元の体とtargetを保持する。
- [ ] 主経路の検査は公理検査と分ける。既存`check_v06_routes.py`の個別根を継承し、MainからN4新cubic等の実使用を追う。umbrellaのlegacy Stopping importだけで失格／合格とせず、個別import閉包・実proof本文・利用可能な依存probeと独立読解のscopeを記録する。
- [ ] 旧83 profile/665比較/5tail、196 core証書、Navi増分を主依存へ戻さない。紙上に残る小幅の場合分けと、有限計算を証明前提にすることを区別する。
- [ ] 未完一覧の空欄は、Task 1の必要入力と50 ID/V06対応を実証拠で全件照合したときだけ空にする。以前のPARTIAL、失敗試行、旧verifier、原稿資料を遡及改変しない。

**Acceptance:** I_MAIN→各実分岐→必要な公刊/代数入力の接続が追跡でき、未証明の数学的入力がない。原稿どおり／十分な別証明／歴史的に不要化した強さを区別する。

## Task 8：全projectのfresh検証と検証器自身の監査

**Files:** Create `scripts/verify_run20.py`, `scripts/check_run20_guards.py`, `audit/run20/EnvironmentAudit.lean`生成用コード、`docs/RUN20_CHANGE_POLICY.json`, unique `verification/run20/runs/<UTC>_<unique>/`。

- [ ] 実行時の最新Run19成功証跡を基準に、全fixture・実質check・V06経路・negative controlsを継承する。現在の最低参考はV06の289 checks/273 fixtures、さらにその中の元Run18 R16の280/268。増えたRun19検査を省略しない。
- [ ] 古いcommand文字列を直接replayしない。出力・EnvironmentAudit・axiom control・固定出力先を新規先または使い捨て隔離先へ写像し、old→newと変更理由を保存する。古いprefix/BASE制約で新runに使えない検証は、新adapterで同じ検査を実行し、旧scriptは改変しない。
- [ ] proof commitを固定し、全project lib/IRとtests/auditのcacheを退避して再構築する。V06改変済みEndpoint下流・新Run19/Mainも対象。固定mathlib cacheの共有とproject coldを区別し、退避範囲・donor検証・依存版を記録する。
- [ ] root buildと最小公開importを検査し、全fixtureを実依存順に実行する。各commandのexit code・警告・生ログ・環境・時間を保存する。`-j1 -M12288`等の実制約を記録し、SIGKILLや失敗試行を成功へ書き換えない。
- [ ] **最終監査はMainの二定理だけでなく、全NSP14 production・全監査受入・全fixtureの宣言/instance/helperを対象**にする。normal/explicit型、module/source hash、実`collectAxioms`、自己依存、import module被覆を保存する。新規ファイル列挙だけの監査や、既存oleanの存在だけによる合格を拒否する。
- [ ] 改変旧公開型をbaseの型記録または隔離base実行と比較する。public moduleのaxiomInfo表示と本当の追加公理を推移依存で区別し、正当なexport stubを誤判定しない。実追加axiomのnegative controlは本番へimportしない。
- [ ] 主定理の展開型がTask 2の元のI_MAINと一致し、全S/k/i、literal target、双方自身の最小変数を持つことを機械記録と独立読解で確認する。H0やsource topを除いた定理だけで代用しない。
- [ ] source manifestには全Lean、全使用script（継承依存scriptも含む）、新verifier/guard/packager、V06原稿receiptと対応表、変更規則、toolchain/mathlib pinを収録する。検証中はHEAD/sourceを固定し、旧全verification/artifactはbytes/filesetを保持する。検証後に書く最終status・review・公開receiptはsource-bound文書と区別し、別のreviewed Git bytesとして配布へ束縛する。bound台帳を後から書き換えて循環認証にしない。
- [ ] 新guardで危険／既存出力先、許可外source変更、frozen contract変更、source/evidence差替え、受入・旧module型・axiom/module coverageの欠落、command脱落、主定理の全称scope縮小、review mismatch、ZIP上書きを拒否する。使い捨て環境で行い、旧guard PASSだけを新guardの認証にしない。
- [ ] `I_PARTITION`と`I_MAIN`の元受入、必要入力、全チェックが完了した場合だけ数学的完了候補を作る。検証PASSと全P14完成は別の欄に記録し、未実装の閉鎖受入をEXPECTED_OPEN成功としてCOMPLETEへ混ぜない。

**Execution command:** `python3 scripts/verify_run20.py --fresh-project-cache --output-dir verification/run20/runs/<new-id>`。旧出力の存在時は書込み前に拒否する。

## Task 9：最終レビュー・完全束・通常Pushを観測して終了する

**Files:** Create `scripts/package_run20_audit.py`, `docs/RUN20_FINAL_REVIEW_JA.md`, new review/decision/publication receipts and `artifacts/NS_P14_LEAN_RUN20_COMPLETE_<unique>.zip`。

- [ ] 全変更・Mainの意味・必要入力・型/公理・V06主経路・検証器/guard/packagerと全raw証跡を独立した最終レビューのscopeにする。sourceを凍結し、指摘は修正・必要再検証の後に閉じる。未解決Critical/Important/Minor/pending/declinedを残してCOMPLETEにしない。
- [ ] proof commit、evidence commit、reviewed commit、検証summary／source／evidence manifest、review本文とdecisionを正確なGit bytes/hashで束縛する。review後に数学sourceが変われば新snapshotで再検証する。docs-only変更もscopeと一致を確認する。
- [ ] 全P14のCOMPLETE判定には、無条件I_MAIN・I_PARTITION・必要なRun19出口・V06維持・全検証・レビューの一致を必須にする。途中成果のZIPは正直にPARTIALとし、全体完成の代用にしない。
- [ ] ZIPは参照するレビュー本文、凍結契約、Main最小入口、完全なsource/evidence manifest、必要なlicense/provenance、再現手順を実際に含める。全entry/hash/CRC・重複・path安全性・既存出力拒否とarchive不変を確認する。
- [ ] 「完全な再現checkout」と呼ぶ場合は、継承scriptも含む実行ファイル被覆を満たす。依存packageを含まないproof/evidence bundleなら、正確なGit proof SHAと固定依存の取得・実行手順を添え、範囲を正しく表示する。
- [ ] 最新work/監査修正を明示fetchし、並行変更を保持・統合して通常commit/Pushする。数学差分なら必要な検証へ戻る。force Pushせず、実remote SHA一致と最終cleanを確認する。Push前の成功をレビューに先取りさせない。
- [ ] 最終報告に主定理の実名・全称型、I_PARTITION/I_MAINと必要入力の閉鎖、元の任意体とliteral target、全検証・許容公理、V06対応、レビュー、proof/evidence/review/ZIPのbinding、配布URL、実Push SHAと残務を載せる。

## 終了条件

**元の全数値半群・任意体・全iについて、双方自身の最小表示でactual完備接錐のBetti比較を証明した無条件の公開I_MAINが存在し、全域分割・全必要入力・V06主経路・fresh全検証・未解決ゼロのレビュー・不変な配布物・通常Push/remote/cleanまで揃ったときだけRun20および全P14 Lean化を完了とする。**

本書の作成時点でRun19完了は公開上未確認である。実行開始時の確認で更新し、本書のPushをRun19/20の数学的完了、全P14完成、クロススレッドへの実行依頼の送信と扱わない。
