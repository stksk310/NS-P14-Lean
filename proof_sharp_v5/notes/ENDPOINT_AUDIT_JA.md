# 端点経路の監査・採否記録

読解基準：`345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`（`origin/work`）。
新規本文：`proof_sharp_v4/chapters/03_ENDPOINT_JA.md`。
本ノートは数学的読解と export の静的照合の記録であり、Lean の新しい cold rebuild の成功記録ではない。

## 採用した変更

| 元の節・補題 | 採用先 | 区分 | 数学的な理由 | 対応する正確な Lean export | 新規形式化 | 状態 |
|---|---|---|---|---|---|---|
| V02§12.1 / E_CORE | E-CORE | 整理 | 固定次数の offset 単射性から実単項式核を一度確認 | `NSP14.Endpoint.Data.coreToG_surjective`, `coreToG_kernel_span` | 不要（既存 statement） | 紙上証明・既存形式化あり |
| V02§12.2 / E_COORD | E-FIBER | 整理 | prefix 消去を有限内部語生成・高さ・Artin 性の共通根拠に | `NSP14.Endpoint.Data.exists_minimal_internal_word`, `minimalFiber_budget`, `coreP_minimalCount` | 不要 | 紙上証明・既存形式化あり |
| V02§12.3 / E_KERNEL | E-KERNEL | 統合 | 全競合の必要十分性・clamp の実現・Mとの交わりを一度に証明 | `NSP14.Endpoint.Data.actual_dead_iff_forbidden`, `actualDeadFiber_eq_inter`, `actualFiberModuleEquiv` | 不要 | 紙上証明・既存形式化あり |
| V03 E_STOP→E_HOMOLOGY の依存辺 | E-FIBER→E-TOR | 依存の削減 | E有限性は有限内部語生成、rank0は`v^m=0`から従い、明示的停止はEulerの入力に不要 | `NSP14.Endpoint.Data.actualEndpoint_rank_zero`, `endpointHomology_balance` | 既存コードの import 最小化を実施するなら別作業。既存コードは保持 | 紙上で依存削減済み |
| V02§12.4 の停止式 | (E-STOP) | 保持・監査用配置 | 全jを尽くす有限停止は具体核の検査に有用。単なる付録移動を短縮と数えない | `NSP14.Endpoint.Data.competitorFiber_stopping` | 不要 | 紙上証明・既存形式化あり |
| V02§12.5 (E13)–(E14) の N の角による R の正確な計算法 | 主比較から除外 | 必要以上に強い中間結果を削除 | 比較に必要なのは実Rの定義と上界。N=M∩Tは保持し、M/N→E/Tのsocle単射とTの角だけでR≤Rhatが閉じる | 精密な実装は `SoclePoints.lean`, `SocleCorePoints.lean`, `SocleCorners.lean`, `AdjacentCorners.lean` に保存。主出口は `actualSocleProductMap_injective`, `actualR_le_Rhat` | 不要。精密結果自体は削除していない | 当該共通経路では不要性を確認。全体の他枝からの使用有無は統合時確認 |
| V02§12.6 / E_BOUNDS | E-RESOURCES | 統合・可読性改善 | carry総和とfloorの総和を表示し、R≤W−uを3行で確認。高さ上界とは分離 | `NSP14.Endpoint.Data.carry_sum_one`, `residueCeiling_sum`, `competitorZ_sum_bound`, `coreP_le_wordVolume`, `actualR_le_Rhat` | 不要 | 紙上証明・既存形式化あり |
| V02§12.5–12.7 / E_HOMOLOGY・E_TRANSFER | E-TOR | 共通接続の統合 | 実核Kの長さPC−PGと端点H1のPGが相殺するため、幅別にPC=PGなどを仮定しない | `NSP14.Endpoint.Data.actual_kernel_compensation`, `actual_core_endpoint_bound`, `completed_core_endpoint_bound` | 不要 | 紙上証明・既存形式化あり |
| V02§12.9 / E_ARTIN | E-ARTIN | 保持・一元化 | parent/child第一行と符号付き単位minorの高次行は別根拠。共通資源を使うが無理に同一証明へ抽象化しない | `NSP14.Endpoint.artin_first_harmonic`, `artin_first_third`, `artin_first_fourth`, `artin_first_signed`, `artin_first_five`, `artin_positive_rows` | 不要 | 紙上証明・既存形式化あり |
| V03 IV.23 の減算形 | E-GEN の加法形 | 表現の置換 | 自然数飽和減算の feasibility が不等式そのものに入り、topも同式で扱える | `NSP14.Endpoint.Data.actual_positive_rows_add`, `actual_endpoint_rows`; 元のsource出口は `NSP14.NumericalSemigroup.narrow_endpoint_rows` | 不要（すでに既存Leanに加法形あり） | 紙上証明・既存形式化あり |
| V02§12.8 / E_TWO | E-TWO | 保持・一元化 | q=2だけの単項式核を使い、内部sigmaと端点Rを混同せず四行を一度で導出 | `NSP14.Endpoint.Data.two_internal_monomial_kernel`, `internalSigma_point_count`, `QCore_two_betti_one`, `QCore_two_betti_two`, `actual_two_all_rows`; 元のsource出口は `NSP14.NumericalSemigroup.narrow_endpoint_two_rows` | 不要 | 紙上証明・既存形式化あり |

「整理」「保持」は数学的仕事自体を消していない。実際に不要化した仕事は、共通移行における明示的停止への依存と、実RをNの全角から正確に求める依存である。Tの角の上界、全長い表示の核同定、実核補償、PGとPCの区別は残る。

## 他章への正確なインターフェース

- **E-TOR**：EH、同じ元のcoreとactual Gに対し、全i≥0で`beta_i(G) <= b_i(QC)+PC*C(q,i-1)+R*C(q+1,i-1)`。i=0、top、aboveも本文に証明。
- **E-RESOURCES**：`PC<=W`, `R<=Rhat=min(W-u,u*max(Hx-2,0))`、`W>=u`。反射のHxへ交換しない。
- **E-ARTIN**：任意体、q≥2、標準次数付きArtin商A=T/I、I1=0。harmonic/third/fourth/signed/fiveと全positive行を供給。
- **E-GEN**：EH、QCの同じHilbert列に対する第一行floor評価、および全i≥1の加法形 `beta_i+C(q+1,i+1)<=PC*C(q+1,i)+Rhat*C(q+1,i-1)`。
- **E-TWO**：追加仮定q=2のみで `(beta1,beta2,beta3,beta4)<=(PC+sigma+1+R,2PC+sigma+3R,PC+3R,R)`、Rhatへの置換可。

## 直接読んで照合した範囲

`proof_structure_v3/work/ENDPOINT_PART.md` 全文、V02§12.1–12.9、`auditability_search/LATER_READABILITY_AUDIT.md` 全文、`docs/RUN16_PAPER_CORRESPONDENCE_JA.md`、および次の本番ファイルの関係する定義・定理・証明：
`CoreMap`, `CoreKernel`, `MinimalWords`, `MinimalBounds`, `ActualKernel`, `Quotient`, `Stopping`, `CarrySums`, `CompetitorBounds`, `CoreArtinBasis`, `Volume`, `SocleInjection`, `SocleBounds`, `HomologyBalance`, `ArtinQuotient`, `Compensation`, `FullTransfer`, `StandardArtinRows`, `ArtinRank`, `FirstRow`, `PositiveRows`, `RowPackage`, `TwoInternal`, `TwoRows`, `TwoMonomial`, `InternalSocleBasis`, `Normalization`。
その他の依存ファイル全部を独立に再証明したとの認定はしていない。上記exportの再ビルドは本作業の他の検証記録と区別する。

## 境界・任意標数性

1. EHではq≥2ゆえu≥3で、`u-2`の飽和減算は通常の整数差と一致する。
2. `W-u`は`W>=u`確認後に使用。`Hx-2`はmax(Hx−2,0)の意味。`PC-PG`も実全射の次元比較後に使用。
3. `i-1,i-2`は紙上では負添字規約を用い、Leanの`coreRemainder`はi=0をguardしている。
4. `i=q+2`は`beta<=R<=Rhat`、`i>q+2`は全変数Koszulの消滅。topを`q+2-i`等で割らない。
5. q=2でQCが単項式であることを証明した。一般qへの単項式性の拡張は行わない。
6. rank下界のminorは整数の±1。標数2でも有効で、標数間rank一致は使わない。parent/childの分数重みは有理数の計数である。
7. gcd(m,u)=1を追加せず、停止周期はu/gcd(m,u)。m=du+2等の物理境界は本章の追加仮定ではなく、EHを満たす限り全証明に入る。

## 保留した短縮案

端点二変数の特殊証明をordinaryの一変数cutと一つの抽象的spectral sequence補題へ統合する案は採用していない。実核補償の相殺は似るが、ordinaryには同jump strataと資源列の追加構造があり、現時点では抽象化による紙上監査負担の減少を証明していない。本文にこの未確定案を混ぜていない。
