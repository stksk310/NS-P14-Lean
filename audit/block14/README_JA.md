# Run14 独立監査：Green・同一cut・offset・actual towerと資源・Sidon

2026年11月10日（JST）。対象：`stksk310/NS-P14-Lean`。
最終提出：`fbfa5debe3daa115b610ecc72dedc8fd52a817ca`。
Run13基準：`d8556dc615b1e1633379f4567e9e795b3f1c8ae3`。
Run14途中版`8040c90`と、取り込まれたRun13再現性修正`aa6bf4c`も区別して照合した。

**判定：指定されたRun14の数学的範囲として合格。検証手順のP2を1件再現し、修正・再検証・workへのPushまで完了した。**
全49 coreファイル・4,357行の構成と型、実対象への接続を確認した。
新しい修正必須の数学的欠陥は見つからなかった。
実行側の実装レビューは参考資料として読み、本監査では検証の再実行・全coreの明示型抽出・独自のLean検査と有限計算を行った。
添付・保存文書内の指示は資料として扱い、ユーザーの監査依頼と区別した。

## P2：過去の絶対出力パスの再利用 — 修正済み

提出時の`scripts/verify_run14_continuation.py`は、旧検証記録に含まれるcommandを再利用する。
fixtureの順序は依存に沿っていたが、`-o`に元の`/workspace/NS-P14-Lean/...`が残っていた。
そのため別checkoutではfixtureを別のbuild領域へ書き、consumerが自身のbuild領域で見つけられない。

隔離worktree・空のproject test cacheから、提出スクリプトそのものを実行した。
buildと13旧試験の計14コマンドが成功した後、`predecessor_13`（JumpBounds）で
`tests/Run12Fixtures.olean`欠落を再現した。
[原出力](as_submitted_console.log)・[失敗結果](as_submitted/result.json)を保存した。

既存`compile_test`を使い、過去のLean commandの出力先だけを現在のrootから作り直す修正を適用した。
ユーザーの継続許可に従い、[修正commit 20aadbf](https://github.com/stksk310/NS-P14-Lean/commit/20aadbf7011692eb3bfffef49029e2c5e416ef3d)をworkへ通常Pushした。
数学的ソース、元の検証記録、既存ZIPは変更していない。

修正済み実スクリプトを同じ別checkoutで`--fresh-test-cache`から実行し、
**50/50コマンドがexit 0、警告なし**で通過した。
[修正後の検証記録](../../verification/run14_reproducibility_fix/verification.json)と
[対応説明](../../verification/run14_reproducibility_fix/README_JA.md)を別ディレクトリに保存し、提出時の原本は復元した。
このP2は監査完了時点で未対応ではない。

## 再検証・型・公理依存・成果物

- 固定公式Lean `4.36.0-rc2`、commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`を使用。
  mathlibは`139105d28c7685a154cb3093f79edb2e16708099`。
  build済み数学ライブラリを利用し、project test cacheは空から開始した。
  固定9依存のrevisionと追跡ソースのclean状態も確認した。
- 50検査はlibrary build、旧43検査、新受入3本、歴史的未完命題の型とその証明、公理監査を含む。
  coreは途中版11ファイルと続行38ファイルの計49、Run14受入は計7ファイル。
- 全3,217環境宣言の公理依存と、新規544宣言の型等の記録は提出版と一致した。
  さらに[独立collector](collect_core_types.py)で**全49 module・699 core宣言**の通常型・explicit型・公理依存を現在のLean環境から抽出し、
  途中版185件と続行版514件の提出記録に完全一致することを確認した。
  自動生成定義・instance・projection・constructor・recursorも含む。
- 依存は`propext`・`Classical.choice`・`Quot.sound`の部分集合。
  proof erasure後の`axiomInfo` stubは`collectAxioms`で実依存を確認し、自己公理依存を拒否した。
  49 coreソースに`sorry`・`admit`・`unsafe`・`native_decide`・外部実装差替え等なし。
- 旧171証明・試験・固定環境ファイルはRun13基準から不変。
  最終manifest48件も元の提出commitと一致し、現在の修正との差は検証スクリプト1件のみ。
- COMPLETE ZIPの890メンバー、内部manifest889件のhash・ファイル本体・提出commitの3者が一致。
  ZIP SHA256は`1bacf872e073a5ea8dba23b6d4222fe35f4de99309964869b99612c07153b964`。
  [整合性結果](integrity.json)に依存revision等を保存した。

## 数学的な主要接続

| 対象 | 確認した内容 |
|---|---|
| 任意標数のGreen基礎 | 最大rankのpencilについて、kernelの像が元のrangeへ入ることを実minorの非消滅で証明する。最大rankを非等方ベクトルで達成できる場合と、全平方が0のalternatingの場合を分け、2で割らない。有限次元性とInfinite kを保持している。 |
| 同一flagの全prefix | 双線型積の実商、cutImageのsup、第三同型による次段の商を使い、独立形式を順に延長する。同じ元の積・同じflagについて全prefixの次数2上界を証明し、別々に選んだcutの評価を混ぜない。 |
| actual Aとの接続 | A₁×A₁→A₂を実積から作り、live factorizationで全A₂を張ることを証明する。双線型商からactual ideal商への全射でGreen上界を運ぶ。二次span全体を殺すcutを構成し、actual次数2 prefixの分解から高次消滅を導く。 |
| 一つのcut・体 | r=max(2,p)、e≥3、2≤r≤e−1。p<2では同じ一次空間内で独立列を延長する。有限体ではRatFunc(k)上でcutを一度選ぶ。拡大が無限・同標数であることを証明し、原有限体へcut自体を戻すとはしない。 |
| Pの意味 | Pはr個の形式的変数の多項式環。S₀への写像で実一次形式を送り、Aの作用像に関係があることを許す。形式の線型独立性を証明する。現consumerは形式的Pと検証済み作用を使い、Pを未証明のままS₀の部分環と同一視しない。 |
| least offsetと安定化 | 正元表示からleast offsetを最小化し、最短実現が非x原子だけから成ることを証明する。ω=b+Lm、ord(ω)≤L≤l、q+L≥lでord(ω+qm)=L+q。粗い一様boundは有限性だけに使う。 |
| 鋭い体積 | least-offset prefixの最小性・剰余の無重複、level初到達時の非原子Apéry剰余を数える。levelが経路上で単調とは仮定しない。least-offset順のrankを有限順列にし、L−1≤min(δ,rank−1)からδ(e+δ/2−3/2)を得る。 |
| 有限性・全terminal | 安定化を先に証明し、全terminalとそのsuccessor headの有限性を導く。Apéryと非Apéry headを分けたactual基底からA/N/Tの有限次元性を得る。最小headだけへの制限や、無限次元のfinrank=0を使わない。 |
| 実tower | FₛはAの実斉次ideal。Uₛ=A/Fₛ₋₁と実高次数idealからX/Mを作る。K=Fₛ/Fₛ₋₁の生存headが次数≥s+1にあることを使い、0→K→M→X_(s+1)→0をS₀上で証明して同じPへ制限する。X_(ν+1)=0。 |
| 同jump・生成元 | KをRun12の実ascending stratumへS₀線型に同定し、同じcutで次数差sを保持する。二次spanから高次の形式倍写像の全射性を導き、X/Mの底次数生成を証明する。さらに変数倍部分加群=次次数truncationを証明し、実augmentation商と底次数を同定する。単なるspanning familyから極小性を推測しない。 |
| 唯一の資源H | 実Uₛの次数次元からHを一度だけ定義する。Apéryの区間[0,sρ−2]、terminalの区間[p,p+d−2]に対応する実基底と同定。同剰余の区間の非交差から全tでHₜ≤m−1、telescopingからΣH=Σ(Lρ−1)≤δVを得る。 |
| headと同時上界 | H₀=δ、H₁+a=δ+ell、ell≤e−1。選んだ同じcutの形式倍写像からH₁≤rδ。r≥3の場合だけ三角数の下界とhead capを使う。Hはラベルcardとして体に依存しないため、拡大体cutのhead評価を元の同じHへ運べる。 |
| actual Sidon | actual Q₂のpairへの単射と最大次元の個数一致から、平方を含む全二次積をlive Apéry基底へ同定。0・一次/二次の衝突も排除して、0とe−1個の非x原子からFin eのAperyPairDataを構成する。標数2、偶数・合成数mも許す。 |
| 数値全行 | 同じcutと同じHからNumericalClosure.Dataを構成し、actual SidonからBoundaryを供給して、既存の数値all_rowsへ通す。r=e−1からQ₂最大を導く系にはr≥3を保持する。 |

Run14の現APIにP→S₀のinjectivity exportはないが、現在の結論には不足しない。
後続がPを文字通り部分環と扱う場合は、線型独立形式からその同定を証明する必要がある。
これは作成済みRun15指令のTask 1にも明記した。

## 独自Lean境界検査

[BoundaryChecks.lean](BoundaryChecks.lean)の7定理と1定義が、警告・追加公理なしで通過した。

- 有限体F₂では、非零tかつ1+t≠0となるtが存在しないことを証明した。
  generic lineの非零点回避にInfinite仮定が必要なことの対照である。
- RatFunc(F₂)²上の対称双線型積μ((a,b),(c,d))=ad+bcを構成した。
  全平方0だがμ((1,0),(0,1))=1で、非零のalternating branchを実際に検査した。
  この実積が張ることと、独立な1形式による二次全消滅cutをLeanで証明した。
- 任意のactual半群・剰余・qについて
  `ord(ωρ+qm)=Lρ+q ↔ lρ≤Lρ+q`を追加で証明した。
  原実装の安定化の十分条件に、least-offset最短長から逆向きも導いたもので、m=1・零剰余も含む。

## 独立有限計算

[check_models.py](check_models.py)は提出実装や検算値をimportせず、次の二通りを独立に計算する。
Apéryとleast offset/最短語は剰余graphのDijkstra、orderは最長表示のDPで求める。
実head商の乗算は生存指数とorderから構成し、GF(16)のGaussian eliminationでcutと形式倍写像を検査する。

[454半群](finite_models.json)で全検査が通過した。
GF(16)では同じ独立形式列を保持してGreenの全prefixを検査し、必要ならr=2まで延長し、
各実tower stageの形式倍全射、kernelへの作用の閉包、商写像との可換性、短完全列の次元を確認した。
**同一cutの作用検査は86,679件**。
これは有限体で具体的に見つけたcutの検査であり、Infinite仮定を外した一般Green定理の主張ではない。

Hをactual生存headから直接数えた値と、二種の区間から数えた値が全tで一致した。
全tail cap、H₀、head恒等式、mass恒等式、鋭い体積予算、rankごとの既存数値rowとの比較も確認した。
非零terminalを持つ113例、非零tailを持つ312例、δ>0で体積等号となる23例を含む。
最大Q₂は111例で、偶数m=8の〈8,9,11〉、maximal cut r=3の〈13,14,17,19〉も含む。
一方、〈6,7,11〉はr=e−1=2でもQ₂が最大でなく、guardの必要性と整合する。

least-offset経路でlevelが下がる例は67件あった。
例えば〈6,7,11,16〉では、非x原子7のprefixの剰余3→4でLは3→2となる。
実装のlevel初到達を数える証明が、誤った単調性やL=Apéryのorderに依存していない点を照合した。
有限計算は一般証明の補助であり、全半群・全体・P14の認証に代用していない。

## 認証範囲と後続

Greenの必要形・一つのcut・offset安定化と鋭い体積・actual tower/生成元商・同一資源列・Sidon・数値全行比較が今回の範囲。
歴史的`RemainingGoals.lean`の5命題も同じ型で証明され、productionがそれらを未証明引数に使っていないことを確認した。

actual Tor-to-row、一般算術列の公刊Betti証明、actual targetとの同定、ordinaryのactual Betti全行閉鎖はRun15。
数値の`ActualWitness.all_rows`を、そのBetti比較まで完成したものとして扱わない。
狭幅側・端点・残る公刊入力・最終P14の完成も本監査から推論しない。

Block11のP3文書指摘（`verification/block11/README_JA.md:97`の「後者」）は歴史的原本に残っている。
Run14由来の欠陥ではなく、既存の修正提案として継続管理する。

## 再現

固定toolchainをPATHへ設定し、この監査branchのrootで実行する。

```sh
python3 audit/block14/check_integrity.py
lake env lean audit/block14/BoundaryChecks.lean > audit/block14/boundary_checks.log 2>&1
python3 audit/block14/collect_core_types.py
python3 audit/block14/check_models.py
python3 audit/block14/check_results.py
```

修正スクリプト自体の再実行は`python3 scripts/verify_run14_continuation.py --fresh-test-cache`。
標準出力先の提出原本を更新するため、原本保存が必要なら別checkoutで実行する。
対象の修正後commitを固定し、後続Runのsource追加後に同じRun14集合を仮定して実行しない。
