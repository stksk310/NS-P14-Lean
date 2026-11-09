# 原文を変更しない補正・scope notes

## E01 — 補助waterfill一般化の符号仮定

対象：R57 `adaptive/ARBITRARY_CUTOFF_ENVELOPES_AND_OLD_FORMAL_OBSTRUCTION.md`、37–52行の一般式(2)。具体的な正重みの式(1)とは区別する。
原文は「nonincreasing weight sequence」だけで、総質量「at most W」の最大値を満量充填としている。tailに負の重みを許すと成立しない。

厳密な最小反例：\(h_0=0,W=1,c_1=1,c_t=0\ (t>1),w_0=0,w_t=-1\ (t\ge1)\)。実行可能な \(h_1\in[0,1]\) に対し最大値は0（\(h_1=0\)）、原式(2)の満量値は−1。

**採用する限定的な補正。** 有限のcutoff Tが存在し、\(W\ge h_0\)、\(w_t\ge0\ (t\ge1)\) を明記する。これが今回の実際のcap q=m−1・有限Wの適用範囲である。全capacityがW−h0未満なら全entryを満たす。無限capacityが境界へ漸近する場合は最大値/上限と極限規約を別途定義するため、本archiveはその一般化を必要な定理として採用しない。

**補正後の証明。** 非負重みなので余った質量を充填して目的値を減らさない。i<j、h_i<c_iかつh_j>0なら、\(\epsilon=\min(c_i-h_i,h_j)\) をjからiへ移して目的値は \(\epsilon(w_i-w_j)\ge0\) だけ変化する。有限Tまでこの交換を行えば最初のT−1を満たしTで残量を置く式(2)となる。容量不足の場合も同様。R57の \(W_j(t)\) は正であり、主証明のD=δによるdual上界・200係数・解析tailも負重み一般化を使わない。

原文の一般文には数学的な仮定不足が存在する。これはP14反例でも主鎖の破綻でもない。原文を黙って書き換えず、反例・必要な補正・非影響範囲を別紙に固定する。

## E02 — 改名前の参照

`DIAGONAL_FIRST_SCALAR_ALL_DEFECTS.md` はR57 ZIPにその名で存在しない。補助waterfill 4,086 ray証明の実在名は `adaptive/AUXILIARY_WATERFILL_4086_RAY_PROOF.md`。主経路は `adaptive/FIXED_DELTA_SCALAR_GLOBAL_PAYMENT.md`。原ファイルの改名参照を未回収証明として二重計上しない。

## E03 — narrow被覆と後続の未完機構

R40-WALLは正規化u<mを閉鎖し、m>wのnarrow sourceはu≤w<mなので既済範囲。R51–R53の sparse/primitive narrow がopenという文をP14本体の未被覆と読むと累積被覆と矛盾する。canonical ledgerは、これらを後続の特定PAY/注入機構の未完成、または古い残課題記述として扱う。R54 all-narrowは別の証明を与えるので、同じsource領域の新発見と数えない。

## E04 — 版・ID・推論の向き

R07の同名RETURNにはSHA `edaefc0e…`（部分版）と `94f9334a…`（全defect6版）がある。ローカルR07-R01も内容が異なる。runとIDだけで同一視しない。R21の実行evidence ZIPと数学RETURN ZIPも別。restoreのdefaultは数学RETURNを選ぶ。
R27-K01はR27-F01の後の系であり、F01の前提へ戻すと循環になる。R47 D16→E273は一方向。R47 c2=2,ell≤1の一般δにはR46-SCを使う。
