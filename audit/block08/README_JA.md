# Block08 独立監査

2026年11月10日（JST）。判定：**実数値半群からのmultiplicity・Apéry・原子・order・数値headの基盤は合格。Block08に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`ae53ad026a55a663bfb295866317d30f8aa72fd3`。
`NSP14/Semigroup/` の6ソースを照合した。
提出された証明・検証記録は変更していない。

## 検証結果

- Block08 manifestの81件すべてが一致。
- 同梱Block08 ZIPの82ファイルすべてが対象コミットと一致し、ZIPのSHA-256も添付の値と一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- ビルド、6ソースの再検査、新テスト、Block01〜07回帰、既存の2監査検査の17コマンドが終了コード0。
- 新規85定理と証明付き定義 `terminalHeadEquiv` の86宣言は完全名を照合した。既存106件も含め、計192件の公理依存は保存ログと一致。依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- 前七ブロックの証明ソース・テスト・固定環境はBlock07監査対象時点から変更されていない。

固定環境はLean v4.36.0-rc2とmathlib `139105d28c7685a154cb3093f79edb2e16708099`。
ビルドは前ブロックの監査でソースから構築した同じ固定依存を再利用した。

## multiplicityとApéry

入力は、実際の加法部分モノイドと、そのconductor以降がすべて所属する証明。
conductorの最小性は要求しない。
multiplicityは正元の最小値として構成され、各剰余の元もcofinitenessから実際に作る。
Apéry代表の存在・最小性を未証明のフィールドに置いていない。

Apéry集合の濃度m、一意分解 `x=ω+qm`、predecessor不在の特徴付けは正しい。
自然数減算を使う箇所には、`ω≤x` または実際のpredecessorの存在がある。
0を含むApéryの扱いは、切り捨て減算 `x−m` をそのまま負の整数と同一視する形になっていない。

追加Lean検査では、carrierが等しい二つの構造はconductorの証拠が異なっても同じmultiplicityを持つことを証明した。

## 原子とorder

原子は正のindecomposable元であり、m以外の原子はApéry内にある。
原子集合の有限性・生成性・任意の生成集合に含まれる最小性を順に証明している。
eはこのactual原子集合の濃度であり、`0<e≤m` は結論として得られる。

`HasLength` は正の半群元への分解長を表し、その長さには有限上界がある。
最大長の各因子が原子であることと、任意の原子表示長がorder以下であることを別々に証明し、
原稿の最長最小生成元表示長との一致を保証している。

orderの意味を使う定理は必要な所属条件を保持している。
追加Lean検査では、半群外の元について `order x=0` となることを証明した。
従って、`order x=0 ↔ x=0` の所属仮定は取り除けない。

## Apéry次数の計数

次数0は{0}、次数1はm以外の原子、次数2以上の濃度はactual deficit `m−e` となる。
二次層の濃度≤δと、各Apéry元のorder≤δ+1は正しい。

最長原子表示から一原子を外すと、残りもApéryでorderがちょうど1下がる。
これにより途中の全次数が存在し、次数2以降の異なる代表をhigh集合へ単射にする証明は有効である。
ここで数えているのは数値集合であり、未構成の商Qのfinrankと同一化したとは扱わない。

## terminal/headとlive条件

terminalと非Apéry headはorderを使う数値ラベルとして定義される。
`x↦x+m`、逆 `y↦y−m` の全単射は、逆側のpredecessorの存在まで証明している。
terminalは正、jump≥2、対応するhead次数≥3。
liveなbase条件ではjump非減少、liveなhead条件では非増加となり、同jumpの仮定からlive条件の同値を得る。

追加Lean検査としてΓ=⟨4,5,11⟩を構成した。m=4、11は原子で、
`order11=1, order15=3, order19=4`。
11はterminalで15が対応する非Apéry headとなる。
この例ではjumpは0で1、11で2、15で1。

- x=0,g=11ではbase側はliveだがhead側はliveでない。
- x=11,g=4ではhead側はliveだがbase側はliveでない。

同jump仮定を外した無条件の数値的live同値は、両方向とも破れる。
これは数値条件の検査であり、加群作用やglobalなT≅Nについての反例を構成したとは扱わない。
実装も数値ラベルの全単射と、仮定付きのlive条件だけを主張している。

## 独立した動的計画法

278個の有限生成数値半群を独立に計算し、以下を確認した。

- 166,800点の所属・原子表示最大長、44,480点の正元表示最大長との一致。
- Apéry全要素1,396点の次数・degree chain・δによる上界。
- 41,094点のApéry分解、44,758点のterminal/head対応。
- 277,870組のlive条件・jump比較。

入力生成元が冗長な114例も含み、eを入力生成元の個数と誤同定していない。
ℕのm=e=1、Γ=⟨3,4⟩、Γ=⟨6,7,15⟩、追加のΓ=⟨4,5,11⟩も一致した。
Γ=⟨6,7,15⟩の最小conductorは24であり、提出例で使う証拠30とも矛盾しない。
terminal等の走査結果は検査した有限prefix内の値であり、terminal全体の有限性を認証した記録とはしない。
有限検査は補助検査であり、一般の結論はLeanの普遍証明による。

## 合格範囲と残る接続

V02 §2および台帳A10–A11との数値座標段階の対応は有効。
actual semigroupからのm・e・δ、Apéry代表、最長原子表示長と数値ラベルは今回構成されている。

未完はactual completed-semigroup tangent coneとの環・基底同定、A/T/N/Q、
同jump stratumの加群同型、jump上限、least-offset・volume・cut・towerの資源構成である。
最大actual Q₂からのpairデータ、Tor/Bettiへの接続、O_COORD全体・P14全体も今回の合格範囲に含まない。
Γ=⟨3,4⟩でactual m/eを持つpairデータを渡す例があっても、一般の最大Q₂の橋が完成したとは扱わない。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。
既存17検証は `python3 scripts/verify_block08.py`、独立追加検査は次で実行できる。

```sh
lake env lean audit/block08/SemigroupChecks.lean
python3 audit/block08/check_semigroups.py
```

既存verifierは提出側の検証ログを更新する。今回の独立実行ログはこの監査ディレクトリへ分離して保存した。

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[独立した有限検査](semigroup_finite_checks.json)

[ビルド](build.log)／[Basic](basic_recheck.log)／[Apéry](apery_recheck.log)／[Atoms](atoms_recheck.log)／[Order](order_recheck.log)／[次数計数](aperygrading_recheck.log)／[Heads](heads_recheck.log)／[統合テスト](tests_and_axioms.log)／[追加Lean検査](semigroup_checks.log)
