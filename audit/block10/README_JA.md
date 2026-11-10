# Block10 独立監査：全次数付き代数・actual x核・head商

2026年11月10日（JST）。対象：`stksk310/NS-P14-Lean`。
対象コミット：`791a2c94eda09479d0582f30726669c6d28fbc7b`。
直前のBlock09：`1d7c4a8a088ecd37648fa5afeb7c35421e2a6f59`。

**判定：合格。代数的半群環のassociated graded全体、actual x核とprincipal ideal商の基底として、修正必須の欠陥は見つからなかった。**
完備半群環との比較、N/Qと同jump加群、資源列・Tor/Betti・P14全体の完成は認証範囲に含めない。
提出レビューは参考資料として読み、本監査ではソースの読解、全検証の再実行、独自の境界検査を行った。
資料中の作業指示とユーザーの依頼は区別して扱った。

## 再検証の結果

- 隔離した対象コミットのスナップショットで、提出検証の全20コマンドがexit 0。警告なし。
  build、新規7ソース再検査、テスト、Block01–09回帰、既存2監査を実行した。
  [replay](replay/)に提出ログを上書きしない形で保存した。
- 全新規71宣言（35定理・26定義・2abbrev・8instance）と旧252件、計323件の公理依存報告を独立照合。
  すべて提出ログと一致し、依存は`propext`・`Classical.choice`・`Quot.sound`の部分集合。
  構造instanceの証明も対象で、`sorryAx`・追加の数学公理なし。
  新規ソースに`sorry`・`admit`・`unsafe`・`native_decide`等なし。
- 旧22証明ソース・9テスト・固定環境3ファイル、計34ファイルはBlock09のhashと一致。
  固定依存9リポジトリの実revisionも一致し、追跡ファイルに変更なし。
- manifestの106エントリ・ZIPの107メンバーが対象コミットと一致。ZIPのSHA256も一致。
  元の証明・検証記録・ZIPは変更していない。
- 独自Lean検査[KernelHeadChecks.lean](KernelHeadChecks.lean)の11例と補助証明が警告なしで通過。
- [独立有限計算](check_tangent_models.py)が278半群で通過。
  単項式の結合則480,384件、選んだ最大4指数上の全係数ベクトル249,366件、核259,374件、像の実predecessorによる持上げ24,734件、
  非斉次多項式の環演算とhead商の積10,008件を検査した。
  係数環はℤ/2ℤ・ℤ/4ℤ・ℤ/5ℤ。詳細は[tangent_finite_checks.json](tangent_finite_checks.json)。

## 証明の接続

| 構成 | 監査した内容 |
|---|---|
| 全直和の環 | 各GₙはBlock09の実冪の商。双線型積を再利用し、結合則・単位元・交換則を代表の環演算へ帰着する。次数の等式と代表の等式を両方保持し、異なる次数型を誤って同一視しない。 |
| k代数構造 | 次数0の定数単項式を使い、乗法と既存の商加群のスカラー作用の整合性を証明する。自然数・整数の埋込みも同じ実代表に由来する。 |
| 全体の座標 | 各次数の線型同値をDFinsuppにまとめ、Σₙ{v : order(v)=n}≃Sで添字を整理する。`tangentBasis_eq_initial`で全基底がactual初期単項式と一致する。 |
| 座標shiftの核 | `coordinateShift`はlive係数だけをv+mへ移す。単射なのは指数移動v↦v+mであり、deadを消す線型写像全体ではない。live矢印の無衝突から、核がterminal支持の有限和全体に等しい。 |
| 座標shiftの像 | 非headの各指数にはactual live predecessorがある。各支持単項式をそこから持ち上げ、任意の有限和で像の逆包含を得る。指数集合の有限性は仮定しない。 |
| actual x乗算 | `xMultiply`はGでの右からのx乗算。座標shiftとの共役を全基底で示し、線型性で任意の元へ拡張する。核・像の全体の同定はこの接続を経由する。 |
| actual核の基底 | `xKernelEquiv`は実際の乗算の核とterminal有限支持座標の線型同値。`xKernelBasis_eq_initial`で基底ベクトルが実初期単項式であることを証明する。 |
| actual head商 | head係数制限の全射性と核=乗算像を証明し、さらに`Ideal.span {x}`のk部分加群とその像を同定する。`HeadAlgebra`はこのactual principal idealによる環の商で、単にhead空間と定義した対象ではない。 |
| 基底と次数別作用 | `headBasis_eq_initial`・`head_initial_ne_zero`が実商クラスとの一致と非零を保証する。`xMultiply_of`が全体の乗算とBlock09の次数別`xAction`を接続する。 |

環・係数座標・座標shiftは任意の可換係数環で構成される。
actual核/商の完成した接続と非零判定は非自明可換環を仮定し、体や標数0には限定しない。
型の未使用変数の省略も確認し、非自明性を省略した補助定理が、実際に非零判定を使わないことを確認した。

`tangentCoordinates`と`headQuotientEquiv`は線型同値である。
前者を通常の畳み込みを持つ半群環との環同型と扱ってはいけない。
Gの単項式積にはorderの余分な跳びによる消滅がある。
またTとAの基底は全体の線型基底であり、今回の構成だけで全head集合の有限性やglobalなT≅Nを認証しない。

## 独自検査の意味

actual半群⟨4,5,11⟩を生成元表示で独立に定義した。
m=4、order(11)=1、order(15)=3なので11はterminal、15は非Apéry headである。
4はliveで、8=4+4はactual x乗算の像に入る。

任意の非自明可換環kとc,d∈kについて、

- x(c[11]+d[4])の全座標は、8に係数dを持つ単項座標に等しい。
- 従ってc[11]+d[4]がactual x核に入ることはd=0と同値。
- actual環商G/xGでは[8]=0、[15]≠0。
- c[15]+d[8]の商座標は15に係数cを持つ単項座標。異なる次数の和も処理される。
- actual head商の1は非零。スカラー・整数の埋込みは元の加群作用と整合する。

以上をLeanで検査した。ℤ/4ℤで核・商の同値を使えること、零環でもGの環・線型座標が定義され全元が0になることも確認した。
整域性を仮定して係数の消去を正当化した箇所はない。

有限計算は、全体のlive/killed単項式積と、次数別に通常の多項式代表を掛けて次数和へ射影する積を比較する。
任意係数ベクトルの核・head制限の核について、必要なlive predecessorを実際に構成して像を照合する。
商の両方の代表に実際のx倍を加えても、head座標と積のhead座標が変わらないことを検査した。
有限の追加検査であり、Leanの一般定理の代用、完備化比較、terminal/head全体の有限性の証明ではない。

## 原稿対応と未完範囲

V02 §2 / V03 `O_COORD`のGの座標、Tの基底、A=G/xGのhead基底への接続に対応する。
[変更台帳A15–A17](../../docs/LEAN_PAPER_ALIGNMENT_JA.md)は実際のLeanの型・証明と一致する。
「Tはdead矢印の始点に支持を持つ」とする説明に、指数移動の単射性と任意の有限和への延長が補われた。

原稿のGは完備半群環k[[S]]の接錐であり、今回組み立てたGは代数的k[S]のassociated graded。
両者の比較定理は未完である。
Nがactual斉次イデアルとなる構成、QのApéry基底と次数別次元、同jump加群、jump上限、
offset/volume/cut/towerのactual資源、最大Q₂からpairデータへの橋、Koszul/Tor・target BettiとP14全体も残る。
Tの基底と非Apéry headの数値対応から、globalなT≅Nの加群同型を導いてはいない。

## 再現

Lean `v4.36.0-rc2`（commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`）、mathlib `139105d28c7685a154cb3093f79edb2e16708099`。
固定toolchain・manifestの依存を利用し、リポジトリrootから実行する。

```sh
python3 audit/block10/replay_verify.py
lake env lean audit/block10/KernelHeadChecks.lean
python3 audit/block10/check_tangent_models.py
```

`replay_verify.py`は提出スクリプトからroot/outputの解決と説明だけを変更し、元の`verification/block10/`を保持する。
最終checkoutでの追加確認は[prepush.json](prepush.json)。
判定・hash・固定依存・全公理報告は[review.json](review.json)と同じ監査ディレクトリに保存する。
