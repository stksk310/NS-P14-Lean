# Run17 原稿・原典対応台帳

未完の定理を実装済みと数えない。最終判定はclosure statusと実Lean exportを照合する。

## 原典と使用単位

- Matt DeVos, *A short proof of Kneser's addition theorem for abelian groups*, Theorem 1。
  URL: https://www.sfu.ca/~mdevos/papers/kneser.pdf
  2026-11-13取得、3頁のweb PDF抽出のSHAを`verification/run17/sources/provenance.json`に記録。
  実際の和集合のstabilizer、商での非周期性、portionと最小stabilizer、二cosetの場合分け。
- S. Savchev / F. Chen, *Long zero-free sequences in finite cyclic groups*,
  arXiv math/0602568v1 (2006-02-25), §§2–4、Theorem 8。
  URL: https://arxiv.org/html/math/0602568v1
  2026-11-13取得、web HTML抽出二窓のSHAを同じprovenanceに記録。
  Prop1: positional部分列和の真の増加。
  Prop2: 1-termのprogression/coset構造と一意性 (a,bは原典で証明を引用)。
  Prop3: maximal extension。Prop4/5: behaving整数列。
  Lemma6: 1-termを末尾へ移す極値置換。Theorem7: maximal behaving部分列。
  Theorem8: long条件から生成元、その逆unitによる一括正規化。

取得本文は実行scratchで照合し、監査束には出典・取得範囲・web抽出hashを記録する。
PDF/HTML原本bytesのhashとは主張しない。

## 再利用する形式証明

Kneserの実証明ソース:
https://github.com/YaelDillies/MiscYD/tree/f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba/MiscYD/AddCombi/Kneser

作者 Mantas Bakšys / Yaël Dillies (2023)、Apache 2.0。
`MulStab.lean`→`NSP14/Additive/KneserFinsetStabilizer.lean`、
`Kneser.lean`→`NSP14/Additive/KneserCore.lean`。
元の著作権表示とlicenseを保持。取得commitの原ファイルhashと変更を記録する。
未完成の別証明`KneserRuzsa.lean`は採用しない。
同じ固定mathlib上でソースから検証し、外部oleanや結論axiomを導入しない。
群一般の有限集合版から、指定の有限可換群と実AddSubgroupの型へ接続する。

## 原稿に残す差分

反復和は独立なn項の選択、0項は{0}。n倍像とは区別する。
SCは値の集合ではなくFin位置の列。unitの代表和はNat、法は同じD.u。
実sourceにunit変換や反射不変性を仮定しない。

SCの実装は十分な代替証明としてV. F. Lev,
*Zero-sum-free sequences with few subsequence sums*, §2 Claims 2–5とTheorem 2の
connected-rearrangement方針を採用する。
URL: https://math.haifa.ac.il/seva/Papers/SavChenY.pdf
順列を存在量化する代わりに、元の位置の有限集合に対するConnected導出木を使う。
sharpの一意性は`S.erase 0⊆b+S`からの二回逆移動で直接証明し、
引用に依存するcoset構造やmaximal zero-free extensionを不要にする。
同値な末尾操作・反復同値項は全て位置を保持する。原典の結論を入力にはしない。
SCの最終exportは元の凍結命題そのものを証明し、代替方針の補題だけを閉鎖とは数えない。

## 証明済みexport対応

| 内容 | Lean export (NSP14.Additive内、EndpointはNSP14.Endpoint.Data内) |
|---|---|
| X_KNESER完全thickening形 | kneser、証明本体Finset.add_kneser |
| 任意Hのcoset計数・実商の非周期性 | card_thicken、quotient_stabilizer_preimage、quotientImage_stabilizer |
| 最終実stabilizerでの反復 | stabilizer_iterated_le、kneser_iterated |
| 生成集合のceil半分増分 | proper_sum_growth、generated_sum_growth |
| 個々はnonunitでもよい三点gcd版 | threePoint_coprime_growth |
| 四点例外の実H=位数2 | fourPoint_small_growth |
| u=2hのantipodal表示と非例外成長 | twoCoset_antipodal、fourPoint_growth |
| X_SCの一般単一unit・Nat総和 | savchevChen、savchevChen_positive |
| 二値列のラベル/個数同時交換とmodular relation | savchevChen_twoValue |
| 重複を保持するmultiset/List | zeroSumFree_multiset_iff、zeroSumFree_ofFn_iff |
| 実正規化a_i集合のcard・生成・距離 | Endpoint.residueAlphabet_card、residueAlphabet_generates、residue_distance_iff |
| Wの有限尾和・成長上界・q=2二次上界 | Endpoint.wordVolume_tail、wordVolume_growth_bound、wordVolume_two_bound |
| 任意選択の実端点因子と1≤K<長さ | Endpoint.internal_zero_selection_factor |
| 実QC生存から一般SC・二値SCへ | Endpoint.surviving_internal_word_SC、surviving_twoValue_SC |

凍結した`audit/run17/RequestedGoals.lean`の二Propは、
`audit/run17/ClosedGoals.lean`の`kneser_closed`と`savchevChen_closed`で追加前提なく閉じる。

三点のgcd wrapperでは、m=u+1,d=1の補助Endpoint.Dataから既証明の到達性を使う。
実consumerのDを変更する操作ではない。四点の群補題はu≥8より強く、
正位数の全巡回群で証明している (card4の前提は保持)。
SOCLE三角形、R<c₀、混合語長≤u/2、最終計数・target支払いはRun18–20へ保持。
