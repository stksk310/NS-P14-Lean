# 最小B: true narrow e≤4 の原典・必要祖先

2026-11-09。rootの新r2/r3補題でordinary e=3,4を処理し、当監査のW(e≥5,u<m)を接続する場合、幅側で残すBは **物理幅 w=g_e−m≤m−2 の真正e≤4** だけでよい。

ここでw=du、uは正規化幅。u<mとtrue narrowは同義でない。du≥m−1のe≤4 sourceはordinary新補題へ回し、古いR27-A02を呼ばない。

以下のsource根は

  source_material/NS_WIDTH_P14_CANONICAL_PROOF_HANDOFF_R01_R57_20261109/04_HISTORICAL_THEOREMS/

である。R33のG03は **exactly five generators** と明記しており、e≤4の根拠にしてはいけない。

## e=1,2,3

- e=1の数値半群はN、completionも同じ。
- e=2の接錐は2変数のhypersurfaceなのでβ=(1,1)。targetの実embedding dimensionは≥2でβ_1≥1、残るsource行は0。独立の有限campaignは不要。
- e=3は公刊定理: Lan–Tu–Vu, *Betti numbers of the tangent cones of monomial space curves*, Theorems 1.1,5.2, arbitrary field。arXiv:2307.05589v1、Acta Math. Viet.49 (2024),347–365、DOI 10.1007/s40306-024-00546-4。全P14比較を明記し、narrow限定でないのでそのまま適用できる。
- 添付原文での正確な参照: `R01_LITERAL_PROOFS.md` L943 (`ORIGINAL R01/research/agent_sources/source_audit.md`)、§C=L1065–1077。監査文書hash `4a0d621ba417a4c1cf67670472f3488599445994fa85097c9bbb5e03b29907c8`。このsource auditは原文の所在を示すもの、公刊定理そのものの独立再証明ではない。

## e=4 の組立て

全域をまとめた原定理は `R27_LITERAL_PROOFS.md` L3397:

  ORIGINAL R27/research/root/R27_F01_ALL_GENUINE_FOUR_GENERATORS_JA.md
  sha256 073ace051c126704a011100efea10f5d9a6b7c93bb0456fe631fd6b68d7100f0

ただしF01の枝I(physical wide)は最終証明に不要。必要なのは以下二枝のみ。

### d=1: primitive true narrow

`R27_LITERAL_PROOFS.md` L4334:

  ORIGINAL R27/research/a/R27_A01_PRIMITIVE_FOUR_ALL_ROWS_SUPPORT_CAPACITY_JA.md
  sha256 defb8fb07b36c3de12b2df5fe4c0645cffc58759a6eb0934c98fa6c124c6f276

量化は0<a<b<w<m,gcd(a,b,w)=1、任意体、実target幅w、全行。true narrow w≤m−2はこの範囲内。

必要な内容:

1. §§2–5: 初期coreの2面支持、pure powers、exact有限coreリスト、実最小禁止単項式の5支持計数から、全m>wに一様なβ_1(G)≤U(a,b,w)。この時点でmは式から消える。
2. §3.1–3.2: Savchev–Chen, *Long zero-free sequences in finite cyclic groups*, Discrete Math.307(2007),2671–2679、arXiv:math/0602568、DOI10.1016/j.disc.2007.01.012。長さ>w/2のzero-free列の標準形から混合word長≤floor(w/2)。これはW(e≥5)にはなかった、e4 primitive枝固有の外部標準入力。
3. §6: w≥48は U≤3w²/8+23w/4−12、targetとの差は (w²−50w+104)/8。w=48+zなら分子z²+46z+8>0。
4. §7: 3≤w≤47の全13,921 primitive offset pairを厳密整数評価。単なるm有限gridでない。U>F_minの例外は(1,w−1,w)、3≤w≤10だけ。
5. 例外w3はsource=target。w4..10,m≥w+2は下記R24-N02のboundary familyだけで足りる。m=w+1の七境界はtrue narrowではないため、最終のこのBには不要（ordinary新補題に回る）。
6. 全i≥2は下記R26-A01を継承する。

### d≥2: nonprimitive true narrow

`R27_LITERAL_PROOFS.md` L3905:

  ORIGINAL R27/research/root/R27_D01_OFFSET_GCD_COMPRESSION_ALL_WIDTH_JA.md
  sha256 8c667fdefe6aa95284dcf0686bf997bcb8b75b366fe024b8471d749a02bb0b71

D01-Bの仮定はd≥2,m≥2u+1。true narrowではm≥du+2≥2u+2なので自動的に成立。

§§2–5は紙上証明: 正規化offset core、長い表現の長さがdずつ増える競合、actual endpoint ideal、P/R/socleの上界、実第二微分rankを保持し、V≥2uのtarget容量へ正係数多項式で全行を支払う。有限checkerは回帰であり、この定理に有限campaignは必要ない。

## primitive高次行の直接祖先

`R26_LITERAL_PROOFS.md` L3459:

  ORIGINAL R26/research/rank/R26_A01_PRIMITIVE_FOUR_HIGH_ROWS_AND_FORCED_RANK_JA.md
  sha256 b76ca9ec6f5fde4985e1b5153df77a247d33421de5cbca630e7a7c90af8c080c

必要なのは真narrowに限ったe4、高次全行。0<a<b<w<m,gcd=1という量化を維持する。

- 実endpoint二重複体の零次行K(y,z;Q)からc_2≥P−socle(Q)、β_2≤2P+3R+socle(Q)等。
- 内部最小word長≤w−2、競合idealのcorner上界、広幅での紙上容量比較。
- §§6–7: 高次のうち第2行だけに小幅残余w4..10がある。m≥w(w−2)でR=0,Qがcore商に一致する理論tailを先に証明し、w+1≤m<w(w−2)の全4,824点＋108tail familyを計算する。true narrow Bではm=w+1のordinary境界を除けるが、元証明書をそのまま使っても仮定を広げる必要はない。
- 原稿の直接模型はR24-N01、R25-K01。ただし下の新しい一般二重複体論証により、必要な数値上界からR25-K01そのものも除ける。R25-K02は元から対照である。

より古いexact模型:

- `R24_LITERAL_PROOFS.md` L3506 `R24/research/gate_n/R24_N01_UNIVERSAL_ENDPOINT_MONOMIAL_MODULES_JA.md`。実E=k[x,v] residue ideal、competition ideal、全Koszul次数の普遍模型。
- `R25_LITERAL_PROOFS.md` L3144 `R25/research/root/R25_K01_TETRAHEDRAL_RANK_AND_ENDPOINT_CANCELLATION_JA.md`（原headerは `# R25-K01 — 四生成元の全標数グラフrankと実endpoint相殺`）。四面体signed incidence、graph/dual graph rank、原整数単模性による任意体への移送。全eへ外挿しない。

## primitive第一行の小例外に必要なratio祖先は一枝だけ

R27-A01は全ratio cover map/R26-R01をまとめて引用するが、実際の例外はa=1,b=w−1。ratio表のパラメータはh=1,t=w−1、R=floor(w/t)=1、w=t+1。従って全ratio machineryを継承せず、**R24-N02 boundary**だけを直接呼べばよい。

- 所在は `R24_LITERAL_PROOFS.md` L2665 の `R24/research/gate_n/R24_N02_ALL_RATIO_BOUNDARY_COLUMNS_JA.md`。
- 適用条件はt≥2,h=1,w=t+1,m≥w+2。
- R26のexact cover確認は `R26_LITERAL_PROOFS.md` L946 `R26_RATIO_COVER_MAP_JA.md` 第2行。これは適用箇所の照合に使い、scope表だけで定理を証明した扱いにはしない。

## 最小の残るDAG

```text
true narrow w≤m−2, e≤4
  e≤2 → elementary
  e=3 → Lan–Tu–Vu Theorem5.2
  e=4,d≥2 → R27-D01紙上全称証明
  e=4,d=1
      first row → R27-A01
          ├ Savchev–Chen + core/support count + w≥48 polynomial
          ├ w3..47 exact 13,921 offset bound
          └ (1,w−1,w)だけR24-N02 boundary
      higher rows → R26-A01
          ├ R24-N01実模型＋下記の一般2変数Artin/Koszul上界
          ├ 紙上tail
          └ w4..10 exact 4,824 points +108 tail families
```

不要: R27-A02、R18の広幅scope/G03、R26-G01 harmonic wide支払い、全ratio registry、R26-R01の一般wedge、R27の七ordinary境界、R33五生成元定理（W(e≥5)で代替）。

## 判定の限界

ここでは必要原典・正確な仮定・不要枝を特定した。13,921 offset、4,824 endpoint点、108 tail familyの全証明書を新たに再実行したとは主張しない。これらはWと異なり、今の最小Bにも実際に残る有限証明成分である。e4の反例・原文実欠落を確認したという報告でもない。


## さらに新しい祖先除去: R25 graph/TU/c2定理は数値上界に不要

R26-A01/R27-D01が必要とする4本の上界は、実Q_G=G/(x,v)Gを使った一般二重複体から直接出る。Q_Gは内部2変数y,z上のArtin quotientなので、σ=dim(0:_Q(y,z))とするとKoszul EulerおよびH_2=socleから

  b^{k[y,z]}(Q_G)=(1,σ+1,σ).

一方、端点Koszulの長さは(P,P+R,R)。従って

  β_i(G)≤b_i(Q_G)+(P+R) C(2,i−1)+R C(2,i−2),

をi1..4に代入するだけで

  β_1≤P+R+σ+1, β_2≤2P+3R+σ, β_3≤P+3R, β_4≤R

を得る。これはR39 actual-source transferでも使った同じ一般的なKoszul二重複体の上界であり、商のBetti単調性や未知d_2=0を仮定しない。従ってR25-K01の全標数graph rank、全単模性、endpoint相殺の完全公式を必要前提にせず、実endpoint模型からP/R/σだけを計算すれば十分。R25-K02等のmandatory controlsは回帰として保存してよいが最小DAGに含めない。


## 今回追加した実replay（条件付き資格は維持）

OBJECT_INDEXのbyte-rangeから原checkerをSHA-256照合して当workdirへ復元し、次を実行した。

- R27-A01著者standalone: 全13,921 offset、例外(1,w−1,w),w3..10、七ordinary境界が記載と一致。
- R26-A01独立checker: 著者endpoint表を読まずactual最大orderから全4,824点＋108 stable-tail familyを再計算。全第2行比較に不足なし。
- R24-N02著者checker: 周期性で全mへ伝播する16個のTaylor複体を整数unit pivot＋零残余で認証。別の308+192 actual sourceは回帰であり有限全称証明に数えない。

出力の範囲は [N4_PARTIAL_REPLAY.json](N4_PARTIAL_REPLAY.json) に記録した。大きな旧出力はdelta ZIPへ再収録していない。新しいreplayで有限成分の再現性は確認できたが、全祖先の独立査読完了という資格に格上げしない。今回の最終稿でN4を条件付きとして残す方針と整合する。
