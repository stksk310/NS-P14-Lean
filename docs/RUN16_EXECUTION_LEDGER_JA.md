# Run16 ledger — plan: docs/superpowers/plans/2026-11-10-run16-endpoint-kernel-transfer-order.md

基準: 447b7ae782414b739968a2a3009dd3a52ae230d0 (origin/work一致、clean)。
指令: 0cda4e8597ea1bafa8770b851ff2373973ee0e03。2026-11-11 JST開始。
Run15の8目標はClosedGoalsの元の型で証明済み。COMPLETE表示を証明入力には使わない。

Ruling: このmanaged workspaceの既存workブランチを継続する — ユーザー指定のwork更新と全過去の同じ固定環境を保つ — 別の並行writerが現れた場合はfetchして保持/統合する。
Ruling: cloud skillの実行スクリプトはローカルfilesystemの実行可能ファイルとして提供されていないため、同じ台帳/受入/一回の最終reviewをリポジトリ内で管理する — 実際の証明とレビューを省かない — 台帳の更新漏れがあればcompaction後の復旧コストが増す。

## Pre-flight interfaces

| producer → consumer | actual contract | status |
|---|---|---|
| T1 → T2/T3 | 広いEH、同じactual source、真正なq+2原子 | Finset offsetから構成予定。du<mは要求しない |
| T2 → T3/T4 | 実core、全射、有限E加群座標、全Min M | ideal座標を実作用へ接続する |
| T3 → T4 | N=M∩T、全j停止、E有限生成、rank0 | T単独を核と呼ばない |
| T4 → T5 | 端点homology=(PG,PG+R,R)、同じ内部作用 | Gはk有限としない |
| T2/T4 → T6 | QC Artin、実一次独立、PC/W/Hx/Rhat | 一般qでQCは非単項式を許す |
| T5/T6 → final | 同じGのintrinsic full Tor、任意体・全行 | i=0の負添字をguardする |
| Run15 → T5 | correctedActionComparison、有限homologyのみ | 実際の型を確認済み、同じnative作用へ適用する |
| Run12/13 → final | completedGradedAlgEquiv、nativeFullAtom_betti、通常Tor | 実際の型を確認済み、S変数順序を同定する |

## Scope / progress

11 ID: I_NORMALIZE, E_CORE, E_COORD, E_KERNEL, E_STOP, E_BOUNDS,
E_HOMOLOGY, E_TRANSFER, E_ARTIN, E_ROW, E_TWO。すべて未完から開始。

- Task1 in progress: EHを広い算術条件のみで固定し、actual sourceと最小原子を構成する。
- Task2–7 pending。

小補題/ファイル/内部commitをrun終了にしない。証明・回帰・原稿台帳・監査引継ぎ・Pushまで継続。

Task1: raw EH Data/source/atoms/multiplicity/embeddingDimension/width GREEN。
RED: verification/run16/red/EndpointData.log (Endpoint.Data未定義)。
GREEN: lake build NSP14、lake env lean tests/EndpointData.lean → exit0。
具体例は(6,1,[1,3],4)と(7,2,[1,3],4)。後者はdu=8≥m=7を保持。
一般gcdによるcofinite性はmathlib Nat.exists_mem_closure_of_geへ実際に接続した。
同じmを保持し、全offset最小性はactual closure上の分解長とgcd(m,d)で証明。
Task1全体は狭幅正規化と全変数表示の接続が残るため未完。

Task1主要接続: WidthNormalization/Endpoint.Normalization/OffsetOrder/Presentation/CarrierTransport。
元のSの非零offset gcdと各正規化offsetを実最小原子から構成し、同じcarrierと同じmを証明。
同じcarrierの選んだconductorはactual order/graded pieces/実接錐/通常Bettiを変えないことを実証明。
3環の変数数は(q+2,2,q)、全環とactual最小表示はrename AlgEquiv、通常Betti保存へ接続。
Task2 in progress: 二変数degree/offset AddSubmonoidと実monoid algebra coreを構成中。
Kernel/Tor/資源の結論をData fieldに追加していない。

Task2: corePointsの実加法monoid、Core=AddMonoidAlgebra、coreToG環写像、surjective、
全最小表示からの可換図がGREEN。E_COREの残りとして線型kernel=死んだcore単項式のspanを実装中。
Task1の4受入(Data/Normalization/Presentation/CarrierTransport)はexit0。

Candidate (未証明): E_HOMOLOGYのEulerをHilbert syzygy/局所化の代わりに、
x-Koszulの有限homologyとv倍の実mapping cone LESで閉じる。
v^m=0とE有限生成ならH_0(x;G),H_1(x;G)はk有限。
そのself-map vのconeのH三項から直接H1=H0+H2を得る。
Gのk有限性は要求しない。候補段階なのでE_HOMOLOGYを完了に数えない。

Task1 complete (I_NORMALIZE): actual narrow normalization, broad raw EH, actual minimal full presentation, original-source graded/completed/Bettis transport. Six scoped acceptance files including core/coordinates have exited0; root build5668 jobs PASS.
E_CORE complete: actual coreToG AlgHom surjective; coreToG_kernel_span exactly the killed core monomial span; full presentation diagram proved.
E_COORD remains partial: only coordinate index equivalence, no E-module direct-sum/finiteness/short words/antichain bounds yet. Continuing same run.
