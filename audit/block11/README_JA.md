# Block11 独立監査：actual N/Q・斉次性・Apéry Hilbert構造

2026年11月10日（JST）。対象：`stksk310/NS-P14-Lean`。
対象コミット：`a6aac7b345e3e7dbd3ac660468bdd220ecfa7dca`。
直前のBlock10：`791a2c94eda09479d0582f30726669c6d28fbc7b`。

**判定：数学的な実装範囲として合格。証明本体の修正が必要な欠陥は見つからなかった。説明文の軽微な指摘1件あり。**
actual斉次イデアルN、実商Q、その継承次数とApéry基底・Hilbert関数・標準生成・体上のArtin性を監査した。
完備化比較、同jump加群とjump上限、actual資源・Tor/Betti、P14全体の完成は認証しない。
提出レビューは参考資料とし、全ソースの読解・検証の再実行・独自例と有限計算を別途行った。
資料中の作業指示はユーザーの依頼と区別して扱った。

## 指摘：B11-DOC-01（P3、文書のみ）

[提出READMEの97行目](https://github.com/stksk310/NS-P14-Lean/blob/a6aac7b345e3e7dbd3ac660468bdd220ecfa7dca/verification/block11/README_JA.md#L97)の
「後者のactual Apéry集合は{0,5,10,11}、…δ=1、ν=2、Hilbert関数は(1,2,1)」の参照先が誤っている。
直前に追加されたordinary半群{0}∪[3,∞)のApéry集合は{0,4,5}、δ=0、ν=1、Hilbert関数は(1,2)。
表示された{0,5,10,11}等は⟨4,5,11⟩のデータである。
`tests/AperyQuotient.lean`では両例を正しく分離して証明しており、Lean証明・検証結果には影響しない。

修正：「後者のactual」を「⟨4,5,11⟩のactual」へ置換する。
[修正パッチ](README_SCOPE_FIX.patch)を用意し、`git apply --check`が通過した。
対象コミットの文書・manifest・ZIPは保持し、パッチは未適用。重大度・根拠は[findings.json](findings.json)。

## 再検証

- 隔離スナップショットで全26コマンドがexit 0、警告なし。
  build、新規12ソース再検査、新テスト、Block01–10の回帰、既存2監査を実行した。
  [replay](replay/)に提出済みログを上書きせず保存した。
- 新規全120宣言（81定理・29定義・9instance・1abbrev）と旧323件、計443件の公理依存を独立照合。
  全報告が提出ログと一致し、依存は`propext`・`Classical.choice`・`Quot.sound`の部分集合。
  `sorryAx`・追加の数学公理なし。新規ソースに`sorry`・`admit`・`unsafe`・`native_decide`等なし。
- 旧29証明ソース・10テスト・固定環境3ファイル、計42ファイルが前Blockのhashと一致。
  対象と前Blockのgit diffでも同じ42ファイルに変更なし。
  固定依存9リポジトリの実revisionが一致し、追跡ファイルに変更なし。
- manifestの128エントリとZIPの129メンバーが対象コミットに一致。ZIPのSHA256も一致。
  監査では元の証明・検証原本・ZIPを変更していない。
- 独自Lean検査[QuotientChecks.lean](QuotientChecks.lean)の11例と補助証明が警告なしで通過。
- [独立有限計算](check_quotient_models.py)が278半群で通過。
  Apéry基底1,396座標、Hilbert次数1,817件、低次同型834件、Nの積閉包16,680件、
  商の積・代表変更16,680件、次数射影116,940件、live原子prefix 2,480件を検査した。
  係数環はℤ/2ℤ・ℤ/4ℤ・ℤ/5ℤ。[結果](quotient_finite_checks.json)に両具体例の正しいデータも保存する。

## 数学的な接続

| 構成 | 監査した内容 |
|---|---|
| Nのideal性 | Aのactual head基底における非Apéry支持空間から出発。Apéry性の下方閉包により、非Apéry因子のlive積はApéryへ戻らない。dead積は0。実基底展開で任意の係数の和・A全体の乗算へ延長する。 |
| Q=A/N | 分母は上で証明したactual ideal。Apéry係数抽出の核=N、0拡張による全射から、第一同型定理で実商の線型座標と基底を得る。 |
| 単項式と積 | N/Qの基底ベクトルをactual商クラスへ同定する。係数1の単項式積が非零である条件はorderの加法性と和のApéry所属の両方。 |
| 継承された次数 | Aₙ、QₙをGₙからの実写像の像として定義し、その後にexact-order支持空間と同定する。都合のよい次数を座標へ付け直したものではない。 |
| registered grading | 全次数が全体を張ること、任意の和に対する次数の独立性、次数和への積を証明。A/Qの`GradedAlgebra`を登録する。 |
| Nの斉次性 | explicitな係数フィルタが登録gradingの射影と一致し、その射影がNを保つ。mathlibの`Ideal.IsHomogeneous`として成立する。 |
| 低次の自然同型 | Aₙ→Qₙはactual quotientの制限で全次数で全射。非Apéry headの次数≥3よりn≤2では核が0となり、同じ写像が同型を与える。 |
| Hilbert計数 | finite Apéry基底を実商へ運び、体上でdim Q=m、q₀=1、q₁=e−1、q₂≤δ、全高次総量δを得る。有限性を供給してからfinrankを使う。 |
| 標準生成 | 最長の原子表示から一原子を外すと、残りもApéryで積がlive。値に関する帰納でactual非multiplicity原子のクラスがQを生成する。任意の原子分解の積がliveとは仮定しない。 |
| Artin性・最高次数 | 体上の有限加群からArtin環instanceを構成。νは有限Apéry集合の最大orderで実現され、actual Qₙ≠0 ⇔ n≤νとν≤δ+1を証明する。 |

N/Qの構造・基底・積・grading・最高次数は非自明可換係数環を許す。
総次元・Hilbert finrank・Artin性の登録は任意体に対する主張。
dimₖQ=mと一般の`Module.length`の定義との同定は別であり、説明文も区別している。
有限なQからA・N・Tそれぞれの有限性を無断で結論していない。

## 独自検査で押さえた境界

actual半群⟨4,5,11⟩を生成元表示で独立に構成した。
15はorder=3の非Apéry headなのでAで[15]≠0、Qでは[15]=0。
これを使い、**自然写像A₃→Q₃は単射ではない**ことを任意の非自明可換環でLean証明した。
したがってsourceのn≤2という範囲を、n=3へ延長してはいけない。
一方、n≤2の同値の値が自然な商写像そのものであることも確認した。
registered射影によるNの保存と、異なる次数1/2の共通元が0となることを検査した。

別のactual半群⟨5,6,9⟩では、非最小なconductor証拠25を使う。
18はApéryでorder(18)=3、order(9)=1。
従って[18]≠0だが[9]²=0である。**和がApéryという条件だけでは積の非零性は保証されない。**
次数3の実商が非零であることも検査した。
有限計算ではこの種類のApéry内の非加法的な組を15件、加法的だが非Apéry headへ入る組を45件確認した。
後者はGやAで生きる積がQで消える別の理由を検査する。
ℤ/4ℤでもgradingとactual原子による生成が使えることをLeanで確認した。

有限計算ではhead商を作ってから非Apéry idealを取り、Qへ射影する二段のモデルを使用した。
Nの任意係数の元を両方の代表へ加えてもQの積が変わらず、次数射影とQへの射影が可換となることを検査した。
最長原子語の各prefixがApéryでliveな積を持つことも独立に計算した。
これらは有限の追加検査であり、Leanの一般定理・完備化比較・A・N・Tの全体の有限性の証明ではない。

## 原稿対応と残る範囲

V02 §2 / V03 `O_COORD`の(O1)について、代数的k[S]由来のactual対象への接続が進んだ。
[台帳A18–A22](../../docs/LEAN_PAPER_ALIGNMENT_JA.md)は、実際の定義・仮定・証明と一致する。
ν上界の短縮は、実現する連続した次数列とδ個の高次Apéry座標による数え上げとして正当化される。
Qの標準生成自体も別途証明され、後続用途を失っていない。

原稿の完備半群環の接錐への比較、actual S₀表示、同jump strataの加群同型、jump≤νは未完。
A・N・T全体の有限性に必要な追加構成、least-offset/cut/tower資源、最大actual Q₂→Sidonデータ、
Koszul/Tor・target Bettiと全P14も未完。globalなT≅Nの加群同型は主張しない。

## 再現

Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`。
固定toolchainとmanifestの依存を使い、リポジトリrootから実行する。

```sh
python3 audit/block11/replay_verify.py
lake env lean audit/block11/QuotientChecks.lean
python3 audit/block11/check_quotient_models.py
git apply --check audit/block11/README_SCOPE_FIX.patch
```

`replay_verify.py`は提出スクリプトからroot/outputの解決と説明だけを変更し、提出検証原本を保持する。
最終checkoutの検証は[prepush.json](prepush.json)。機械可読の判定は[review.json](review.json)。
