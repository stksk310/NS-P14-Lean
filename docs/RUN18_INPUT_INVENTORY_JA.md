# Run18 入力・受入契約台帳

- 採用work: `c4fd8153f55bb231aab4168a47c1546888fa7ab0`。
- 指令: `131f559a9ad495891f0aab487f969bf91b5a447f` のRun18指令書。内容を変更せず本branchへ収録。
- 実行場所: `/workspace/NS-P14-Lean-run18`、`run18/implementation-20261113`。通常checkoutと既存監査worktreeを保持。
- Run16独立監査: `5ced6cc564e5c69bebcd7a852463091e2e276661`。
- 着手時のremoteにRun17独立監査branchやRun18実装branchは見つからず、workも指令作成時から更新なし。Run17公開版のCOMPLETEと独立監査合格は区別する。
- Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`。既存projectのbaseline build: 5964 jobs、成功。新規moduleをrootへ加える前の結果。

## 実API

| 入力 | 使用する実export | 今回の義務 |
|---|---|---|
| Run15 target | `interval_completed_betti_lower`、`positiveBettiProfile_lower`、`apLowerProfile_monotone` | 物理幅V=duの実targetへ戻す |
| Run16 source | `endpointData_totalBetti`、`fullG_totalBetti`、`completed_totalBetti` | 同じ元のsource・体・最小変数列 |
| Run16 QC/R | `actual_core_endpoint_bound`、`coreP_le_wordVolume`、`actualR_le_volume` | P_Cと元のsocleのまま評価 |
| Run16 Artin | `QCore_first_third/fourth`、`coreHilbert_two_bound` | Qでの重み計数を実Torへ適用 |
| Run17 W | `wordVolume_growth_bound`、`wordVolume_tail_shift` | 有限正部分和の正確な評価 |
| Run17 四点 | `fourPoint_growth`、`CyclicAntipodal` | 五生成元の実coreと各場合の支払い |
| 共通graded Tor | `artinGrading`、`gradedBetti_total` | 非Artin斉次商でも次数piece有限性を確認 |

## BHP/EKの調査範囲と未証明部分

固定mathlibとNSP14の全文を `Bigatti|Hulett|Pardue|Eliahou|Kervaire|lex.*ideal|ideal.*lex` で検索。25行は既存のdegLex/一般ideal等であり、該当するBHP/EKの証明は確認できなかった。語句検索の限定的な結果であり、同値定理の不存在の証明ではない。

GitHub検索の `"Bigatti" "language:Lean"` と `"Eliahou" "language:Lean"` も結果なし。広い検索はCoCoALib/Singular/Macaulay2等の計算コードや文献を返したが、Lean証明として採用できるものは未確認。

公刊指定先: Juhnke-Kubitzke–Venturello, *Graded Betti numbers of balanced simplicial complexes*, DOI `10.1007/s40306-021-00449-8` §2.2 Lemmas 2–3。GitHubにあるMacaulay2の書誌記録はarXiv `1811.03892v1` を指す。Springer本文の直接取得は、この環境のCONNECTで403となり本文を取得できなかった。書誌記録を本文の代用とせず、取得できていない本文のhashを捏造しない。

原稿V02/V03の適用statementは読める。しかし、それだけでは任意標数の圧縮/変形による実Tor比較、lex存在、EK解消の完全なLean証明を供給しない。これらは未証明の義務として保持する。char 0のgin、有限表、数学公理を代用しない。

## 凍結する契約

`audit/run18/RequestedGoals.lean` は証明を含まないProp定義である。`X_BHP_EK`、`W_EDGE`、`W_DENSE`、`W_SPARSE`、`W_FIVE`、`W_CLOSE` の意味を最終台帳の閉鎖判定に使う。BHPは任意体・一般の斉次商・同じ全Hilbert関数・全graded正行。EKはproperなlex商の実極小生成元、内部次数 `deg(v)+i−1`。全域比較は元のSとliteral completionの各最小変数列を直接参照する。

`acceptance/BHPEK.lean` は未証明の公開宣言 `NSP14.Lex.bhp_ek` を要求する受入で、現時点ではその未実装だけを理由に失敗する。失敗を成功扱いせず、通常の通過fixtureとは区別する。
