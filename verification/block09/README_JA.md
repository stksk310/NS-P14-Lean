# Block09：半群環の実イデアル冪・次数付き商・乗算

2026年11月10日（JST）。7ソース・43定理を含む60宣言。
Block01–08のソース・テスト・固定依存revisionは保持する。

## 数学的な到達点

SをBlock08の数値半群、R=k[S]を `AddMonoidAlgebra k S.carrier` とする。
正元単項式の生成イデアルを𝔪とする。任意の可換係数環kについて

- 𝔪はactual原子の単項式でも生成される。
- 𝔪ⁿは、order(v)<nの係数がすべて0である多項式全体と一致する。
- 非自明係数環では tᵛ∈𝔪ⁿ ⇔ n≤order(v)。
- kが体なら定数項写像R→kは全射、核は𝔪。従って𝔪は極大。

正元分解の最長長がactual原子表示の最長長に等しいことはBlock08で証明済み。
今回はそれを仮定に置かず、単項式の冪所属を得るために実際に使用する。

## 次数付き商の構成

`powerModule n` は𝔪ⁿをk加群へ制限したもの。
`nextPower n` はその内部の𝔪ⁿ⁺¹、`GradedPiece n` はこの実部分加群による商。
order=nの指数集合 `DegreeExponent n` への係数抽出は全射で、核は正確に次冪となる。
第一同型定理により

Gₙ = 𝔪ⁿ/𝔪ⁿ⁺¹ ≃ₖ ( {v∈S : order(v)=n} →₀ k )。

任意のconductor証拠Cに対し、order(v)≤nならv<(n+1)(C+1)と示して指数集合を有限化した。
Cの最小性は不要。`gradedPieceBasis` はこの指数集合で添字付けされた実際の商の基底であり、
`gradedPieceBasis_eq_monomial` が基底ベクトルと初期単項式の一致を証明する。

## 商上の積とx作用

代表の積は、どちらかの代表を次冪だけ変えても結果が次冪だけ変わる。
この両側の条件を証明して、双線型写像 Gₙ×Gₚ→Gₙ₊ₚ を構成した。
非自明係数環kでは、単項式の積はorderが加法的な場合にだけ非零で、余分に跳ねれば0になる。

x=[tᵐ]による写像 `xAction n : Gₙ→Gₙ₊₁` もこの商上の積から構成する。
非自明係数環kと任意のactual半群元vの初期単項式について、核に入る条件は
order(v)+1<order(v+m)、すなわちBlock08の `Terminal v` と同値となる。
これは単なる数値モデルへの写像ではなく、実際のイデアル冪の商における判定である。
核全体の基底、head商の基底、加群の同jump同型はまだ含まない。

## ファイル

| ソース | 主な役割 |
|---|---|
| Ring | 半群環、orderで切る単項式イデアル、係数所属判定、積 |
| IdealPowers | 正元分解から冪所属、全冪の同定 |
| RingCoordinates | 定数項の環準同型、極大性、actual原子での生成 |
| GradedPieces | 実冪の商、係数抽出、核・全射・線型同値 |
| GradedProduct | 商上の双線型積、初期単項式のlive/killed判定 |
| GradedBasis | conductorによる有限性、商の単項式基底 |
| TangentAction | x=[tᵐ]の作用、terminalと核の接続 |

## 検証と再現

```sh
python3 scripts/verify_block09.py
```

このクラウドでは `PATH=/tmp/ns-p14-lean/bin:$PATH` を先頭に付ける。
19コマンド：build、7ソース再検査、新テスト、既存8Block回帰、2監査。
新規60宣言（43定理、16定義・abbrev、有限性instance1）と既存192件、合計252公理依存報告を検査する。
証明を含む構成定義、線型同値、商上の積も対象に含める。
依存はpropext・Classical.choice・Quot.soundだけを許し、警告も失敗として扱う。
前Blockの15ソース・8テスト・固定環境3ファイル、計26個のhashを照合する。
過去のログ・manifest・ZIPは書き換えない。

実例はℕ（C=0、m=1）とactual半群⟨2,3⟩（C=2）。
後者でorder(3)=1、order(6)=3なので[t³]²は次数2で0となる。
order(2)=1、order(4)=2なので[t²]²は非零。
第0冪、定数項、差f−fの消去も検査する。

## 残る境界

今回は代数的半群環の各次数と積である。
完備半群環k[[S]]との比較、全直和を一つの次数付き環として組み立てる結合則・単位元の登録は後続。
A=G/xG・Tの全基底・N・Q、同jump加群同型、jump上限、volume/cut/towerからactual資源の構成、
最大Q₂からpairデータへの橋、Koszul/Tor、target Betti入力、P14全体は未完である。
原稿へ反映可能な証明と仮定の対応は台帳A12–A14に保存する。
