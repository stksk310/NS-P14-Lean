# Block05：調和和の障壁と全大rank基点

2026年11月10日（JST）。ソースは [LargeSeed.lean](../../NSP14/Ordinary/LargeSeed.lean)。
Block01–04の証明ソース・テスト・固定依存revisionは保持した。

## 完成した範囲

`large_seed_pos` は、すべての自然数r≥9に対し

G_r(10,a_r)=`gap r (largeCutoff r) 10 (triangular r)` > 0

を証明する。有限個のrankを確認して無限範囲へ外挿する証明ではない。
`harmonic_lt_barrier` はr≥10の全域で調和和の障壁を帰納により証明する。

基点のe=10は有理式を評価する座標である。
r>9でe=10のactual sourceが存在すると主張しない。
actual sourceでe≥r+1となる範囲への移行は、次の差分評価で行う。

## 定義・原稿との対応

| 原稿 | Lean |
|---|---|
| a_r=r(r+1)/2 | 有理数 `SmallScalar.triangular r` |
| 整数三角数 | 自然数 `triangularNat r`、一致は `triangularNat_cast` |
| D_r=⌊a_r/2⌋+1 | 自然数 `largeCutoff r` |
| H_n=Σ_{u=1}^n1/u | `harmonic n`、空和は0 |
| B(r)=r/4+1+9/(2r) | `barrier r` |
| V02 (S9)のT_r | `threshold r (largeCutoff r)` |
| V02 (S12)のT₁ | `thresholdLower r` |
| G_r(10,a_r)=(r−1)(a_r+9)(T_r−H_D) | `seed_eq_threshold` |

`cutoff_bounds` はa_r+1≤2D_r≤a_r+2を両偶奇で証明する。
`cutoff_step` はDの単調性と2(D_{r+1}−D_r)≤r+2を示す。
`harmonic_tail` と `tailWeight_eq` は原稿の調和和と既存の有限tail和の添字を接続する。
基点の `gap` や `upper` を別の近似式で置き換えず、既存定義との等式を証明している。

## 原稿から改善した証明

[対応・変更台帳](../../docs/LEAN_PAPER_ALIGNMENT_JA.md) A05に、最終原稿へ移せる証明を保存した。
原稿の凸性評価と中間の2/rを介さず、各項の上界から

H_{D_{r+1}}−H_{D_r}≤(r+2)/(a_r+3)<B(r+1)−B(r)

を直接示す。右の差を通分すると、x=r−10に関する正係数の四次式になる。
初期値H₂₈<B(10)から帰納し、原稿と同じH_D<B(r)を得る。
これは元の鋭い中間評価「調和和の増分<2/r」まで証明したという主張ではない。

T₁−Bの正係数分解と、床関数の下限からT₁≤T_rを得る部分は原稿のまま。
r=9は旧大rank表の一行だけを直接有理数計算する。
以前のr=4,…,8の大rank表は復活させない。

## 検証

```sh
python3 scripts/verify_block05.py
```

このクラウドでは先頭に `PATH=/tmp/ns-p14-lean/bin:$PATH` を付ける。
build、ソース再検査、Block05テスト、Block01–04回帰、負のシフト検査、
Block02監査の仮定検査を実行する。
新規22定理と既存10+14+7+13件の公理依存を検査し、標準3公理以外を拒否する。
新規定理は完全名も照合し、前4ブロックのソース・テスト・固定環境のhashも照合する。

テストにはr=9・10の境界、a_rの偶奇、自然数除算と有理数cast、
H₀/H₁/H₂の添字、H₂₃の正確な値、T₉、増分比較の正の差7/3190、普遍的な受入口がある。
最終原稿の基点計算用にB(10)−H₂₈とG₉(10,45)の正確な有理数値もLeanで検査する。
数値例は無限範囲の証明の代わりではない。
`interface_before.log` は実装前の不在確認であり、成功記録とは区別する。
現行スナップショットのhashはこのディレクトリのmanifestに保存する。
既存ブロックのmanifest・ZIP・検証記録は履歴として保持する。

## 残る接続

e方向の係数・δ方向の最初の差分の正値性、基点から任意のe≥10・δ≥a_rへの延長、
Block03資源評価との大rankでの合成は次の単位。
actual tower・Tor上界・target余裕・Betti移行、M12・P14全体は未完。
今回証明したのはO_LARGEの無限基点列であり、O_LARGE全体の完成とはしない。
