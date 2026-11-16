# Block10：全次数付き環・actual x核・head商の基底

2026年11月10日（JST）。7ソース、35定理を含む71宣言。
Block01–09の証明・テスト・固定依存は保持する。

## 完成した構成

Block09の実商Gₙ=𝔪ⁿ/𝔪ⁿ⁺¹と、その商上の双線型積を用い、G=⊕ₙGₙを可換k代数へ組み立てた。
結合則・交換則・単位元・整数の埋込み・kのスカラー作用は実半群環の代表へ帰着して証明する。
次数が異なる型の等式は、次数の等式と代表の等式を持つ `homogeneous_mk_eq` で処理する。

`TangentAlgebra` はこの代数的半群環のassociated graded全体。
`initialMonomial v` はorder(v)次数への実クラスの埋込みであり、全体の係数同値

G ≃ₖ (S →₀ k)

と `tangentBasis_eq_initial` によって、これらがG全体の基底と示す。
非自明なkでは初期単項式は非零、積はorderが加法的なら[v+w]、余分に跳ねれば0となる。

## 単項式だけでなく核・像全体を同定

x=[tᵐ]、`xMultiply` はGでの実際の乗算a↦axをk線型写像として束ねたもの。
指数の平行移動v↦v+mは単射。一方、`coordinateShift` はliveな指数の係数だけを平行移動し、
deadな指数は消す線型写像である。後者全体の単射性は主張しない。

`tangentCoordinates (xMultiply a) = coordinateShift (tangentCoordinates a)` を
Gの全基底で証明して任意のaへ延長した。
live矢印の行き先に衝突がないため、核に入る係数ベクトルの支持は正確にterminal集合となる。
像はliveなincoming矢印がある座標の全体と一致する。逆包含では各座標の実predecessorを取り、
支持単項式の和を持ち上げる。

従って非自明な可換係数環kについて

T=ker(xMultiply) ≃ₖ (terminal指数 →₀ k)。

`xKernelBasis_eq_initial` はこの基底がactual初期単項式であることを保証する。
係数が打ち消し合う任意の有限和も含めた核全体の定理であり、単項式ごとの必要十分条件だけではない。

## A=G/xGは実際の環の商

head座標への制限写像は全射で、その核はxMultiplyの像と一致する。
さらにprincipal ideal xGを `Ideal.span {x}` として定義し、そのk部分加群が実際の乗算の像と一致することを証明した。
`HeadAlgebra` はこのactual principal idealによる環の商である。

A=G/xG ≃ₖ (x-head指数 →₀ k)。

`headBasis_eq_initial` と `headQuotientEquiv_initial` は基底と実単項式の商クラスを同定する。
`head_initial_ne_zero` により、非Apéry headもactual商で非零と分かる。
`xMultiply_of` は全体でのx乗算がBlock09の各次数のxActionへ制限されることを保証する。

## ソースの分担

| ファイル | 役割 |
|---|---|
| TangentAlgebra | 実商のgraded ring axioms、全直和の可換環 |
| TangentScalars | degree0のスカラーと可換k代数構造 |
| TangentCoordinates | 全指数への線型同値、全体の単項式基底と積 |
| ShiftCoordinates | live filter、指数移動の単射、座標核・像 |
| HeadCoordinates | terminal核座標とheadへの制限・cokernel |
| KernelHead | actual乗算との同定、核全体、principal idealの実商 |
| KernelHeadBasis | 核/商基底とactual単項式の一致、各次数の作用との接続 |

一般可換環で作る環・係数・座標shiftに、非自明性は不要。
actual核/商の完成した接続は非自明可換係数環を仮定し、任意体を含む。
非零判定にも必ず非自明性を付ける。体の標数は制限しない。

## 検証

```sh
python3 scripts/verify_block10.py
```

このクラウドでは `PATH=/tmp/ns-p14-lean/bin:$PATH` を先頭に付ける。
20コマンド：build、7ソース再検査、新テスト、旧9Block回帰、2監査。
新規71宣言（35定理・26定義・2abbrev・8instance）と旧252件、計323公理依存報告。
構造instanceの証明も検査し、propext・Classical.choice・Quot.sound以外の依存と警告を拒否する。
旧22ソース・9テスト・固定環境3ファイル、計34hashをBlock09 manifestと照合する。

実例はℕ（C=0,m=1、x核=0）とS={0,4,5,8,9,10}∪[11,∞)。
後者でm=4、order11=1、order15=3を実際に証明する。
11はterminal、15は非Apéry headなので、actual Gに非零のx核元、actual Aに非零のheadクラスが存在する。
dead項とlive項の和、同じdead指数の任意係数の和、スカラーと積、結合則・単位元も検査する。

## 残る接続

代数的k[S]から完備半群環k[[S]]へのassociated gradedの比較はまだ別工程。
今回のT/Aの基底は全体の線型基底。Aのhead集合全体の有限性やN/Qの次数付き構造をこのBlockで新たに証明したとは扱わない。
Nがactual斉次イデアルであること、QのApéry基底とq_s、同jump stratumの加群同型、jump上限、
volume/cut/towerからactual資源の構成、Koszul/Tor、target Betti公式とP14全体が残る。
global T≅Nという加群同型は主張しない。
原稿へ反映する証明は対応台帳A15–A17に保存する。
