# Block06：大rank scalarの全域閉鎖

2026年11月10日（JST）。ソースは [LargeScalar.lean](../../NSP14/Ordinary/LargeScalar.lean)。
Block01–05の証明ソース・テスト・固定依存を保持した。

## 完成した範囲

`LargeScalar.large_gap_pos` は自然数r≥9、**有理数**e≥10、δ≥a_rのすべてについて

G_r(e,δ)=`gap r (largeCutoff r) e δ` > 0

を証明する。Block05の基点だけの評価を、任意のe・δへ延長した。
`Resources.scalar_lt_large` はBlock03の同じ資源列の上界を用いて
F_r<δ(V+1) を導く。`F≤upper` やgapの正値性を追加の仮定として要求しない。

actual sourceではe≥r+1≥10、δ≥a_rなので数値範囲を満たすが、
そのactual sourceから資源列を構成することは今回の証明に含まない。

## 原稿との対応

| V02 §11 | Lean |
|---|---|
| 基点のe係数A₀ | `baseSlope`：G_r(11,a)−G_r(10,a) |
| δの最初の差分b₀ | `baseStep`：G_r(10,a+1)−G_r(10,a) |
| (S21)の補正C | `correction`、`seed_slope_identity` |
| C<0、A₀>0 | `correction_neg`、`baseSlope_lower`、`baseSlope_pos` |
| (S23) | `step_identity` |
| (S24)–(S27)のF₁ | `floorStep`、`floor_comparison_identity` |
| b₀の正値性 | `baseStep_gt`：r≥9では5/4より大きい |
| (S28)–(S30)の差分・和 | `quadrant_identity`：有理数シフトの恒等式 |
| (S31)、V03 (O23) | `large_gap_pos`、`Resources.scalar_lt_large` |

## 証明の改善と定義域

[対応・変更台帳](../../docs/LEAN_PAPER_ALIGNMENT_JA.md) A06に、最終原稿へ移せる式と証明を保存した。
床関数の偶奇を分けず、F(D)−F_minの一つの有理式と2D≥a+1で比較する。
大rank枝r≥9の範囲ではa≥4rなので、原稿のb₀>1/4をb₀>5/4へ強化できる。

β=1−α、s=e−10、t=δ−aとすると

G_r(10+s,a+t)=g₀+sA₀+t(b₀−β/2)+β(t²/2+st)。

g₀>0、A₀>0、b₀−β/2>3/4、0<β<1より、すべての有理数s,t≥0で正。
0<t<1で負になるt(t−1)/2を非負と仮定していない。
この形により整数シフトだけに制限する必要がなくなった。
対象のrank範囲はr≥9であり、旧V02のr=4,…,8の大rankルートは復活させない。

## 検証

```sh
python3 scripts/verify_block06.py
```

このクラウドでは先頭に `PATH=/tmp/ns-p14-lean/bin:$PATH` を付ける。
build、ソース再検査、新テスト、Block01–05回帰、負のシフト検査、Block02仮定検査を実行する。
新規15定理と既存10+14+7+13+22件、計81件の公理依存を検査する。
新規定理の完全名と、前5ブロックのソース・テスト・固定環境のhashも照合する。
許容する依存は `propext`・`Classical.choice`・`Quot.sound` だけである。

テストはr=9・10・11、e=10・δ=aの境界、s=t=1/2、有理数シフトの普遍受入口、
任意に遠い位置の非零tailを持つ実際の `Resources` の数値データを含む。
ここでの数値データはactual半群や接錐から構成したものではない。
`interface_before.log` は実装前の不在確認で、成功記録とは区別する。
今回の照合対象はこのディレクトリのmanifest。既存ログ・manifest・ZIPは履歴として保持する。

## 未完の接続

大rankのscalar数値評価は、同じResourcesを入力として全域で完成した。
そのscalarがr≥4の全重み付き行を支配する一般の組合せ評価は後続工程。
actual tower・cutからの資源構成、実際のTor rankへの上界、actual targetの余裕とBettiへの移行も未完。
O_LARGEのactual対象への全接続、M12・P14全体が完成したとは扱わない。
