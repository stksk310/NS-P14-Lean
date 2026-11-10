# 実行スレへの先行指令：Run16 / 端点actual核・停止・全行Tor移行

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun16として、狭幅sourceの正規化、整数coreから同じactual接錐への全射、全競合による正確なkernel、有限停止、端点homology、kernel補償付きTor移行を証明し、一般qとq=2の全Betti行上界を任意体でexportする。

**Architecture:** 同じactual数値半群を固定し、coreの剰余別E加群座標→全競合ideal→actual kernelとの共通部分→端点Koszulの三項→内部変数を加える実比較の順に接続する。coreのArtin商からactual商へのkernelを別途補償し、最後にArtin評価・二内部変数socleを代入する。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python検証。

**Spec:** [全体20 run計画](2026-11-10-p14-20-run-roadmap.md)、[Run14後の再校正](../../RUN14_20RUN_RECALIBRATION_JA.md)、[Run15先行指令](https://github.com/stksk310/NS-P14-Lean/blob/586019b/docs/superpowers/plans/2026-11-10-run15-actual-tor-target-ordinary-order.md)、[V03端点部](../../../proof_structure_v3/work/ENDPOINT_PART.md) IV.1–IV.10、V02 §§12.1–12.9、[carry・kernel補償の監査記録](../../../auditability_search/LATER_READABILITY_AUDIT.md) §§1,7。

## Global Constraints

- これは先行準備。作成時の公開workは`20aadbf7011692eb3bfffef49029e2c5e416ef3d`（Run14再現手順修正済み）。Run14監査記録は`audit/block14-20261110`の`06d31699b6b15069b1b33e701e81b85d4e4ed790`。Run15の完了・exportはまだ確認していない。
- Run16実装はRun15の完了状況と必要exportを確認してから開始する。最新work、Run15のclosure status・未完宣言・監査修正を読み、基準SHAと使う宣言の実際の型を記録する。計画上の宣言やCOMPLETE表示を証明の代わりにしない。
- Run12–13のactual数値半群・形式的/完成接錐・通常Tor・有限homology・体拡大と、Run15で実証明された初期ideal/module・rank・有界比較を再利用する。Run16の端点移行自体に不要なAP/target公式を追加前提にしない。必要な共通補題の不足は可視化して補う。
- 担当11 IDは`I_NORMALIZE`、`E_CORE`、`E_COORD`、`E_KERNEL`、`E_STOP`、`E_BOUNDS`、`E_HOMOLOGY`、`E_TRANSFER`、`E_ARTIN`、`E_ROW`、`E_TWO`。ここで閉じるのはactual sourceの端点上界。狭幅全域のactual interval targetとの比較はRun17–20へ渡す。
- 小補題・ファイル・途中コミットでrunを終了しない。実装、actual接続、修正、必要な検証、台帳、監査引継ぎ、通常Pushまで一つの長いrunで進める。30〜60分を硬い上限にせず、context圧縮後も継続する。20 runは運用目標であり、未証明を完了に数えない。
- 固定環境、既存証明、過去の検証原本・ZIPを保持する。許容公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ。kernel公式、rank Euler、解消存在、Tor比較をaxiomや未証明Prop fieldとして渡さない。
- 以下の新規ファイル名・宣言名は設計候補。既存APIと照合して統一する。原稿と異なる十分な代替証明は可だが、使う仮定と実際に閉じた結論を台帳へ明記する。

## Review Focus

1. **同じsourceと三つの環を保つ。** 全環Sはq+2変数、端点Eは2変数、内部Tはq変数。coreは仮想の別半群への置換ではない。剰余分解はE加群同型であり、環の直積でも内部T加群の成分別分解でもない。
2. **EHの範囲を縮めない。** `0<a₁<…<a_q<u<m`、q≥2、d≥1、gcd(a₁,…,a_q,u)=gcd(m,d)=1。必要なのはu<mでありdu<mではない。gcd(m,u)=1、Cohen–Macaulay性、d=1を追加しない。
3. **kernelと商を区別する。** actual kernelは`N_s=M_s∩T_s`。全j≥1を停止式で尽くす。`Q_C→Q_G`のkernelは一般に非零であり、Betti単調性や`P_C=P_G`を仮定しない。
4. **有限性の場所を守る。** GはE有限生成・rank 0であるが、一般にk有限次元ではない。有限なのは端点homologyとQ_C/Q_G等。Gに有限長Eulerを適用しない。与えられた`MinimalFreeTower`の比較だけで任意対象への存在も済んだとしない。
5. **添字・向き・標数を守る。** 負添字の二項係数は0。Natの`i-1`を無条件に使うとi=0で誤るため、guard又はInt添字で定義する。差・floorは整数/有理数で扱うか非負性を先に証明する。carryとheightは同じ向きのcoreに属する。有理重みを正標数の体内で割らない。

---

## Task 1：actual sourceの正規化とEHインターフェース

**Files:** `Semigroup/WidthNormalization.lean`、`Endpoint/Data.lean`・`CoreMap.lean`等。

- [ ] actual数値半群の最小生成系`m=g₁<…<g_e`、e≥4、actual幅`w=g_e-m≤m-2`から、非零offsetのgcd dと、`u=w/d`、`q=e-2`、正規化内部offset列を構成する。
- [ ] `d≥1`、`q+1≤u<m`、offsetの狭義順序、両gcd条件、`m≥du+2`を証明する。元の半群が文字通り`〈m,m+da₁,…,m+da_q,m+du〉`に等しく、最小原子数もq+2であることを示す。mをdで割った別半群へ置換しない。
- [ ] 共通端点データEHは上のReview Focus 2の広い仮定だけで定義する。狭幅からのconstructorと、任意EHからのactual数値半群constructorを分ける。e=1/2/3や空gcdへこの正規化を無条件に適用しない。
- [ ] 任意EHについてcofinite性・最小性を証明する。長さl≥2の表示から`(l-1)m=d(a-B)`、`l-1=jd`、`a-B=jm≥m>u`の矛盾を得る。全offsetのgcdとgcd(m,d)から生成元全体のgcd 1を供給する。
- [ ] 任意体kで`S=k[x,y₁,…,y_q,v]`、`E=k[x,v]`、`T=k[y₁,…,y_q]`を固定する。Sと既存actual full polynomial presentationの同定、及び形式的接錐と完成接錐の既存比較を同じsourceに対して作る。

**Acceptance:** 元のsourceを入力する狭幅exportと、生のEHからのexportの両方が使えること。EHの段階でdu<mを要求しない。ここから先は全EH・全体kについて証明する。

## Task 2：整数core・actual全射・有限E加群座標

**Files:** `Endpoint/Core.lean`・`CoreMap.lean`・`Coordinates.lean`等。

- [ ] degree/offsetの対(n,B)の実加法monoidから`C=k[s,st^{a₁},…,st^{a_q},st^u]`を構成する。全生成元の次数は1。単項式基底と実積を備え、単なる有限プロフィールにしない。
- [ ] actual最大分解長をordとして、`s^n t^B ↦ (t^(nm+dB))*`（ord=nの場合）、ord>nなら0となる次数付き環全射`C→G`を構成する。固定次数の異なるBは異なる数値指数を与え、核が殺されるcore単項式で張られることを証明する。
- [ ] `0≤r<u`、`ε_r=[r>0]`に対して`B=r+uK`、`n=L+K+ε_r`を一意な非負座標として構成する。xとvの作用がそれぞれLとKを1増やすことを証明する。
- [ ] 内部語α、`|α|≤u-1`から`Bα=Σα_j a_j`、`r=Bα mod u`、`K=Bα/u`、`L=|α|-K-ε_r`を作る。Lの非負性を先に示し、これらの点で実単項式ideal`M_r⊂E`を生成する。
- [ ] prefix剰余の一致から、内部因子u個以上の語に長さl・offset cuの部分語（1≤c≤l-1）を見つけ、`x^(l-c)v^c`への交換で内部因子数を減らす。全coreを上の有限リストで生成できることを証明する。
- [ ] gcd条件による全剰余への到達と最短長≤u-1を証明し、`M_r≠0`、`M_0=E`、`C≃⊕_r M_r[ε_r,r]`をE加群同型として得る。内部y作用が剰余を移すことも記述する。
- [ ] 極小点antichainを構成する。非零rの極小点では`L+K≤u-2`、r=0は(0,0)のみ、`H_x=max L≤u-2`を証明する。

**Acceptance:** actual全射と有限リストからのE加群同型が通常の宣言として使えること。一般qのQ_Cを単項式T商と決めつけない。整数座標の検算だけでactual全射を閉鎖したとしない。

## Task 3：全長い表示・正確なkernel・一様停止

**Files:** `Endpoint/Competitors.lean`・`ActualKernel.lean`・`Stopping.lean`等。

- [ ] (n,B)と同じ数値指数を持つ長い表示は、ちょうどcoreに属する`(n+jd,B-jm)`、j≥1であることを両方向に証明する。
- [ ] 長い側rと短い側sを`r+jm=s+cu`で結び、長い側極小点(L,K)から禁止領域の始点
  `(max(0,L-jd-c+ε_r-ε_s), K+c)`
  を導く。第一座標はIntで計算してからclampする。clamp後も長い側へx冪を掛けて実現できること、c≥1で第二座標のclampが不要なことを証明する。
- [ ] 全j,r,極小点で生成する競合idealを`T_s`とし、actual kernelが`N_s=M_s∩T_s`であることを証明する。実同型`G≃⊕_s M_s/N_s[ε_s,s]`を構成し、元のactual作用へ接続する。
- [ ] `c-ε_r+ε_s≥floor(jm/u)`と、始点の第一座標≤`max(0,H_x-2j)`を証明する。m mod uの0も含め、剰余境界を落とさない。
- [ ] `J₀=floor((u-2)/2)`、`p=u/gcd(m,u)>0`に対して
  `T_s=Σ_(1≤j≤J₀+p) T_(s,j)`
  を証明する。j>J₀では第一座標0、j→j+pで同じr・carryが`m/gcd(m,u)`増加するため後の生成元が既存の倍数になることを示す。j=1だけの検査で代替しない。
- [ ] 各T_sに純v冪があること、actual Gで`v^m=0`、`v^m M_s⊂N_s`を証明する。GのE有限生成と、分数体への局所化等による`rank_E G=0`を得る。

**Acceptance:** 全m,d一様の停止定理から有限計算が正当化されること。停止値より先の任意jを覆い、gcd(m,u)>1・u|mも含む。実kernelをT_sそのものに置き換えない。

## Task 4：端点homologyの正確な三項と一様socle上界

**Files:** `Endpoint/EndpointHomology.lean`・`Socle.lean`・`CarryBounds.lean`等。

- [ ] `Q_C=C/(x,v)C`、`Q_G=G/(x,v)G`、`P_C=dim Q_C`、`P_G=dim Q_G`、`R=dim(0:_G(x,v))`をactual商・作用で定義する。Q_Cの標準次数付きT-Artin商構造、次数1の独立性`(Q_C)_1≃k^q`、次数n≥uの消滅を証明する。
- [ ] Q_C基底は全Min M_s、Q_G基底はその生存点と同定する。Rは`M_s\N_s`に属し、x/v両隣がN_sに入る点で数える。N_sの極小点を`A₀<…<A_t`、`B₀>…>B_t`と並べ、隣接角`(A_(i+1)-1,B_i-1)`のうちM_sに入る点が基底となることを示す。E/N_sのArtin性は要求しない。
- [ ] 端点Koszul homologyのk有限性・T作用と、正確な次元列
  `dim H_•(x,v;G)=(P_G,P_G+R,R)`
  を証明する。中間項はE有限生成・rank 0からのrank Euler等で示す。必要な有限自由解消存在/局所化比較を実証明するか、同等の十分な代替を構成し、Gを有限長と扱わない。
- [ ] 内部ステップの最短語長ℓ_r、ℓ₀=0と最短点(L_r,K_r)を構成し、`L_r+K_r=ℓ_r-ε_r`を証明する。距離予算`W=1+Σ_rℓ_r`（幅wとは別）に対し、antichain計数から`P_C≤W`を得る。
- [ ] T_sの極小点数をz_s+1、最小第二座標をκ_sとする。任意(A,B)∈T_sに対し`z_s≤A+B-κ_s`、`κ_s≥ceil((m-s)/u)`、`Σ_s ceil((m-s)/u)=m`を証明する。
- [ ] j=1の最短点競合で` s_r=(r+m) mod u`、`c_r=(r+m-s_r)/u`、`A_r≤L_r`、`B_r=K_r+c_r`を得る。剰余置換と`Σc_r=m`を示し、次のcarry相殺を省かず証明する：
  `Σz_s ≤ Σ_r(A_r+B_r-κ_(s_r)) ≤ Σ_r(L_r+K_r)+m-Σ_sκ_s ≤ W-u`。
- [ ] `M_s/(M_s∩T_s)→E/T_s`のsocle単射から`R≤Σz_s`を得る。第一座標heightによる`z_s≤max(H_x-2,0)`と合わせ、
  `R≤Rhat=min(W-u, u*max(H_x-2,0))`
  を証明する。差の非負性を明示する。反射coreのH_xやWを同じactual Rに無条件で流用しない。

**Acceptance:** P_C、P_G、Rの異なる意味と、実homologyの三項が追えること。carryの正負両項を保持し、m,d一様性が有限グリッドの観測に依存しないこと。

## Task 5：actual kernelを補償して全q+2変数へ移行する

**Files:** `Endpoint/QuotientCompensation.lean`・`FullBettiTransfer.lean`、必要な`Homological/BoundedKoszulComparison.lean`等。

- [ ] actual T加群完全列`0→K→Q_C→Q_G→0`を構成し、`dim K=P_C-P_G`を証明する。実Tor長完全列と内部Koszul鎖群の次元から
  `b_i^T(Q_G)≤b_i^T(Q_C)+(P_C-P_G)*choose(q,i-1)`
  を得る。i=0は負添字0の規約で正しく処理する。
- [ ] actual二重複体`K(y₁,…,y_q;K(x,v;G))`をSの通常Koszul/Torへ同定する。端点を先に取った第0行が正確にTor^T(Q_G,k)であり、残り二行にはTask 4のactual homologyが入ることを示す。
- [ ] 実有界filtration又はspectral sequenceで
  `β_i(G)≤b_i^T(Q_G)+(P_G+R)*choose(q,i-1)+R*choose(q,i-2)`
  を証明する。必要な有限性はhomologyに供給する。Gを含む鎖群自体のk有限性、spectral sequence退化、内部作用の剰余別独立性を仮定しない。
- [ ] kernel補償とPascalから全i≥0で
  `β_i(G)≤b_i^T(Q_C)+P_C*choose(q,i-1)+R*choose(q+1,i-1)`
  を得る。RをRhatへ換えた版もexportする。全変数βは同じactual完成接錐のintrinsic totalBettiへ接続する。

**Acceptance:** `P_C≠P_G`の場合にも同じ定理を使えること。型の前提にkernel補償・有界比較・homology次元の未証明結論を残さない。第0行、上端、範囲外を含む全行定理にする。

## Task 6：一般Artin評価・二内部変数socle・全行export

**Files:** `Homological/ArtinParentChild.lean`・`ArtinKoszulRank.lean`、`Endpoint/TwoInternalVariables.lean`・`RowPackage.lean`等。

- [ ] 任意体上の標準次数付きArtin商`A=T/I`、Iは真の斉次ideal、q≥2、I₁=0について、実初期ideal・標準単項式を使用する。`A₀≃k`、`h_n=dim A_n`、`P=Σh_n`、h₀=1、h₁=qと有限台を証明する。`b₁^T(A)=μ_T(I)`も実完全列から供給する。
- [ ] 次数n+1の全直接約数が標準となる候補D_nを定義する。子から親への有理重み`α_j/(n+1)`を用い、子ごとの和1・親ごとの和≤`(n+q)/(n+1)`から`#D_n≤(n+q)h_n/(n+1)`を得る。極小初期生成元数`#D_n-h_(n+1)`を数え、実Gröbner division/liftで元のIの生成元数とb₁を抑える。
- [ ] 有理数/整数の不等式としてV03 IV.21の全三形をexportする：
  `b₁≤q+Σ_(n≥1)(q-1)h_n/(n+1)≤(q-1)P/3+(q+1)(q+2)/6`、
  `b₁≤(q-1)P/4+(q+1)^2/4+(q-1)h₂/12`、
  `b₁-P≤q-1+Σ_(n≥1)(q-n-2)h_n/(n+1)`。
  q=5の`b₁-P≤14`も供給する。最後の和の負係数をNat減算で消さない。
- [ ] Koszul微分の係数次数0→1で、i元集合Jに対応する行`(y_(min J),J\{min J})`を選び、I₁=0による実±1 minorを示す。任意標数でrank d_i≥choose(q,i)を得て、全i≥1で
  `b_i^T(A)≤P*choose(q,i)-choose(q+1,i+1)`
  を証明する。標数2でも使用でき、i>qは両辺0になる。
- [ ] A=Q_Cを実際に代入する。Task 5と合わせ、一般qで
  `β₁(G)≤P_C+floor(q+Σ_(n≥1)(q-1)h_n/(n+1))+Rhat`、
  `β_i(G)≤P_C*choose(q+1,i)+Rhat*choose(q+1,i-1)-choose(q+1,i+1)`（2≤i≤q+2）
  を得る。β₀=1、i>q+2の0、top≤Rhatもexportする。floor・減算の型と正当化を明示する。
- [ ] q=2では同次数の純内部語のoffset`na+j(b-a)`の相異性からQ_Cが単項式T-Artin商であることを証明する。一般qへこの単項式性を拡張しない。
- [ ] 内部作用を`r+a_j=s+cu`、`(r,L,K)↦(s,L+1+ε_r-c-ε_s,K+c)`で実現し、Q_Cでは移動先が極小点なら基底元、他は0であることを証明する。内部socle`σ_C=dim(0:_(Q_C)(y,z))`を数え、actual端点socle Rと区別する。
- [ ] 有限長Q_Cの二変数Koszulから`b_•^T(Q_C)=(1,σ_C+1,σ_C)`を得て、全四行
  `β₁≤P_C+σ_C+1+R`、`β₂≤2P_C+σ_C+3R`、`β₃≤P_C+3R`、`β₄≤R`
  とβ₀=1、i>4の0を証明する。Rhat版も出し、後続N4へ渡す。
- [ ] 最終APIはraw EH及びTask 1の狭幅actual sourceから任意体・全行へ到達できるよう揃える。仮定はEH/狭幅の実データと算術条件に限定し、核公式・rank-zero Euler・Artin評価・Tor移行の証明をconsumerに再要求しない。

**Acceptance:** E_ARTINの一般商とE_ROW/E_TWOのactual sourceへの適用を両方確認する。第一Betti行だけ、又は数値プロフィールだけで端点パッケージを完了にしない。

## Task 7：境界・再現検証・closure台帳・公開

- [ ] 各Taskで先に受入型と期待する等式/不等式を固定し、未実装で失敗することを確認してから実装する。`tests/EndpointCore.lean`・`EndpointKernel.lean`・`EndpointHomology.lean`・`EndpointTransfer.lean`・`ArtinRows.lean`等に一般定理の実適用を置く。名称は候補。
- [ ] q=2/一般q、uの最小端、d>1、du≥m、gcd(m,u)>1、u|m、j=J₀/J₀+1/J₀+pと以後、carry境界、height 0/1/2/3、非零kernel、非零R、標数2を検査する。i=0/1/2/q/q+1/q+2/q+3と負添字規約も検査する。
- [ ] 具体例候補はEHをLeanで証明してから使う：`(m,d,a,u)=(6,1,[1,3],4)`（gcd(m,u)>1、P_C≠P_G）、`(7,2,[1,3],4)`（d>1、du≥m）、`(7,1,[1,5],6)`（kernelと端点socleが共に非零）。独立した有限座標モデルの探索値は順に`(P_C,P_G,R)=(5,4,0),(5,5,0),(9,6,1)`であり、これ自体をactual値の証明には使わない。
- [ ] 一般qの非単項式関係の検査候補は`(9,1,[2,3,4],7)`：Q_Cで生存する`y₁y₃=y₂²`を確認する。向きの検査候補は`(8,1,[1,2],5)`と反射`[3,4]`：H_xが異なることを確認し、反射側の値を元のactual上界へ流用しない。
- [ ] 小さな格子はactual最大分解長からの独立モデルと照合し、全競合停止・N=M∩T・P_G/Rを検査する。有限検算を全m,dの形式証明へ置き換えない。狭幅正規化の試験と、狭幅外でもEHを満たす試験を区別する。
- [ ] `scripts/verify_run16.py`等は実依存順でビルドし、試験専用importを含め空のproject test cacheから再現する。出力先は現在のcheckoutに相対化し、別worktreeでも旧checkoutのoleanへ書かない。過去検証は固定commitの記録又は依存を解決した回帰入口で保持する。
- [ ] 全新規宣言・instance・constructor/recursor/自動生成宣言とroot-moduleの公理依存をLean環境から抽出し、許容集合外と自己依存を拒否する。通常/explicit型、所属module、仮定、source/evidence hashを保存する。
- [ ] `verification/run16/`、COMPLETE又は正直なPARTIAL ZIP、`RUN16_CLOSURE_STATUS.json`、未完宣言一覧、進捗・原稿台帳を更新する。11 IDごとにactual入口・主要宣言・全行/任意体の出口・依存証明・試験・残件を対応させる。過去原本を上書きしない。
- [ ] 通常commit/Push後、remote SHAとclean worktreeを確認する。work取得は`git fetch origin refs/heads/work:refs/remotes/origin/work`等で実際の最新SHAを確認する。並行更新は保持して統合し、force Pushしない。

## 終了条件と後続run

**同じactual sourceから、正規化・core全射・全競合kernel・一様停止・正確な端点homology・Rhat・kernel補償付き全行Tor移行・一般Artin/二変数評価までが実証明でつながり、担当11 IDのexportと検証が揃った時にRun16完了とする。**

coreの有限表だけ、j=1だけ、Rの数値推測だけ、P_C=P_Gを仮定した移行、条件付きのhomology/Tor比較だけでは完了条件を満たさない。実際に解けない障害があれば、閉じたexport・未完の正確な型・理由・必要入力を保存し、完了範囲を明示する。

後続へ渡すのは同じ向きの`P_C,W,H_x,h_n,R/Rhat,σ_C`とactual全行定理。Run17のKneser/SC、Run18のBHP/EK・e≥5幅評価、Run19のN4/LTV・小生成元、Run20の全域合成は担当を保持する。Run16の実測で残り配分を再校正し、必要な証明をrun数のために落とさない。

このファイルは実行スレへ貼り付け/参照するための先行指令である。監査スレからの直接送信やRun16の証明実装は行っていない。
