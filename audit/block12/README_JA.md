# Run12 独立監査：actual同jump加群・jump上限・形式級数接錐比較

2026年11月10日（JST）。対象：`stksk310/NS-P14-Lean`。
対象コミット：`6b8d16889ea9b4d88567f0d9ac70391db2a49824`。
直前のBlock11：`a6aac7b345e3e7dbd3ac660468bdd220ecfa7dca`。

**判定：Run12で指定されたactual座標接続・形式級数接錐比較として合格。新規の修正必須の欠陥は見つからなかった。**
全22ソースを読み、S₀作用・実部分加群の商・同じ写像の次数差・全terminal上限・literal k[[S]]の実冪と比較を確認した。
提出済みの実装レビューを参考資料とし、本監査では全検証を再実行して独自の境界検査も行った。
資料内の実行指示とユーザーの監査依頼は区別した。
X_BASIC全体、安定化・資源・cut/tower、Tor/Betti、公刊入力、P14全体の完成は認証しない。

## 再検証と整合性

- 対象commitの隔離スナップショットで全44コマンドがexit 0、警告なし。
  build・22ソース単独再検査・6新規受入試験・全新規公理依存・run計画検査・旧11Block回帰・旧2監査を実行した。
  元の検証原本を保持し、[replay](replay/)に新しいログを保存した。
- 224新規core宣言（127定理を含む）と74名前付きfixture宣言を、提出collectorより広い修飾子・宣言構文の独立走査でも照合し、完全一致を確認した。
  新規298件と既存443件、計741件の公理依存報告はすべて提出ログと一致。
  依存は`propext`・`Classical.choice`・`Quot.sound`の部分集合で、`sorryAx`・追加数学公理なし。
  新規ソースに`sorry`・`admit`・`unsafe`・`native_decide`等なし。
- 旧41証明ソース・11試験・固定環境3ファイル、計55ファイルのhashとgit diffに変更なし。
  固定依存9リポジトリの実revisionが一致し、追跡ファイルはclean。
- manifestの249エントリ、ZIPの250メンバー、ZIPのSHA256が対象コミットと一致した。
  監査で提出済みの証明・検証記録・ZIPを変更していない。
- 独自Lean検査3ファイルの11例と補助証明が、警告・追加公理なしで通過した。
- [独立有限計算](check_run12_models.py)が279半群で通過した。
  filtration作用40,320件、同jump作用20,160件（非零106件を含む）、live split 199,686件、
  formal factorizationと切詰め各898,380係数、実積と次数付き積7,533組・1,212,813係数を検査した。
  [詳細結果](run12_finite_checks.json)に数え方と有限検査の範囲を保存した。

## 数学的な主要接続

| 対象 | 確認した内容 |
|---|---|
| actual S₀ | 変数はactual非multiplicity原子で、個数はe−1。Gへの準同型は実初期単項式へ送り、Gへの全射とは主張しない。TはGのannihilator ideal、NはAの実イデアルとして同じ作用を受ける。A/Qへの全射性を証明する。 |
| 全terminalの上限 | 最長表示を次数ν+1で切る。prefixがApéryならνの定義に反し、そうでなければmを引けるのでτの長い表示を得る。y=0も別に処理し、最小headへの制限や仮定されたcapなしでjump≤νを証明する。 |
| filtration | DₛTはjump≥s、FₛNはpredecessor jump≤sのactual S₀部分加群。実乗算と任意の係数の有限和に対する閉包・反対向きの包含・実次数射影による安定性を証明する。 |
| 実商 | 分母はDₛ₊₁T又はFₛ₋₁Nを分子へcomapしたもの。exact-jump sliceの核が実際の分母と等しく、全射であることから商の座標を構成する。s−1の切捨てを使うascending側の同定と同型には0<sを要求する。 |
| 同jump S₀同型 | 同jumpの両端についてactual乗算の係数が一致し、これを全Gの基底、任意のG元、任意のS₀多項式へ延長する。`jumpStratumEquiv`は実商のS₀線型同型である。 |
| 同じ写像の次数差 | 次数部分をG/Aの実斉次代表元の商像として定義する。その同型で次数pの所属と次数p+sの所属が同値。単項式の次数公式だけで済ませていない。 |
| 端点・退化 | D₂T=T、D_(ν+1)T=0、F₁N=0、F_νN=N。δ=0からactual T=N=0まで接続する。 |
| literal形式級数環 | `PowerSeries k`のうちS外の係数が0である部分k代数を採用。定数項kernelが正元イデアルで、体上では全射性から実際に極大である。 |
| 無限級数の実冪 | order=nのprefix集合の有限性を使い、無限級数の係数を同じprefixへ分配する。有限和f=Σtᵘgᵤを係数ごとに証明し、actual ideal powerとorder条件を同定する。無限和のideal閉性は仮定しない。 |
| 自然な接錐比較 | 自然なk[S]→k[[S]]が係数と冪所属を保存。order=nの有限切詰めで各実冪の商への全射、係数条件で核の一致を得る。商の同値を次数・積・単位元・kスカラーを保つ全体の同値へ組み立てる。 |
| x・核・商 | 初期単項式・x・x乗算の可換性、actual核の同値、principal ideal商Aとその商Qの自然な代数同値を構成する。formal側Nは自然な商同値によるactual Nの像として明示されている。 |

形式級数環の実冪とGの比較は任意の可換係数環で構成される。
`formalMaximalIdeal`という名称でも、一般可換係数環のkernelを無条件に極大とは扱わず、極大性の定理は`Field`を仮定する。
同jump加群・非零判定には既存どおり非自明可換環を使い、任意体を含む。
原稿のliteral k[[S]]を直接構成するため、別の未証明のAdicCompletion同定を仮定する段階はない。

## 独自Lean検査

[FormalChecks.lean](FormalChecks.lean)では、自然な多項式→形式級数の写像の単射性を、係数保存から独立に導いた。
actual半群⟨3,4⟩について、全ての指数3n+3j（j≥0）の係数が1である真の無限級数を定義した。
任意nで実イデアルn乗に入り、非自明係数環ではn+1乗には入らないことを証明した。
n=0を含み、無限級数の有限prefix因数分解・自然な切詰めによる次冪との差・零係数・零環も検査した。

[StrataChecks.lean](StrataChecks.lean)では、actual半群⟨5,6,13⟩を別に構成した。
m=5、ord(13)=1、ord(19)=2、ord(18)=3、ord(24)=4で、13と19のjumpはともに2。
非x原子6による作用が[13]→[19]としてjump 2の実商で非零のまま残り、
同じ`jumpStratumEquiv`でN側の[18]→[24]の非零作用に対応することを任意の非自明可換環で検査した。
また自然な形式級数接錐比較の下で[13]が非零で、xに殺されることも確認した。
orderの上界は有限表の各stepをLeanの`decide`で証明し、全正元分解の長さの上界へ接続した。外部計算値を仮定していない。

[GlobalBoundaryChecks.lean](GlobalBoundaryChecks.lean)では、提出fixtureのactual半群⟨9,10,15,26⟩を使い、
**全体の座標対応`terminalHeadVectorEquiv`がactual S₀作用を保たない**ことをLeanで証明した。
Tでは15が[26]を非零の[41]へ送るが、Nでは[35]との積がorderの跳びで0になる。
これは同jumpに制限する必要性を確認するもので、別の抽象的な加群同型の不可能性を主張するものではない。
sourceの同jump同型をglobalなT≅Nへ拡張していない点は適切である。

## 独立有限計算の範囲

279半群の最長原子表示をDPで計算し、全terminalのprefix内のjump上限とνを照合した。
actual非x原子の多項式をℤ/2ℤ・ℤ/4ℤ・ℤ/5ℤ上で評価し、actual T/Nのfiltration安定性、
両方の商でexact-jumpを取った作用の一致、次数差を任意係数の有限和で検査した。
非零の同jump作用とjumpが変わる作用の両方を含む。

formal側は指数160までの係数について、最長語のprefixによる分配、有限和による再構成、
次冪との差が消える次数切詰め、普通の級数積と次数付き商の積の一致を検査した。
零係数環も因数分解・切詰め検査に含む。
この部分は有限prefixの追加検査であり、本当の無限級数に対する一般証明はLeanの定理が担う。
terminal/head全体の有限性やTor/P14を有限試験から結論していない。

## 原稿対応・継続事項

V02 §2 / V03 `O_COORD`の指定範囲が、actual S₀・T/A/N/Qとliteral形式級数接錐に接続された。
[台帳A23–A27](../../docs/LEAN_PAPER_ALIGNMENT_JA.md)は、仮定・写像・次数と未完の境界を正しく記録する。
特にjump上限の直接prefix証明は、原稿の生成次数・最小headを経る議論を短縮し、結論を弱めていない。
形式級数の有限因数分解も、一般的な完備化定理への未証明入力を増やさず比較を閉じている。

残るのは、actual安定化・offset体積・cut/towerと共通資源列、最大Q₂→Sidonデータ、
Koszul/Tor・target Betti・公刊入力・全P14と最終原稿照合。
Run12の完成からX_BASIC全体やこれらの完成を推測しない。

Block11監査のP3文書指摘（具体例の「後者」）は過去の原本に残っている。
これはRun12で導入された欠陥ではなく、以前の[修正提案](https://github.com/stksk310/NS-P14-Lean/blob/audit/block11-20261110/audit/block11/README_JA.md)として継続管理する。

## 再現

固定Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`を使い、rootから実行する。

```sh
python3 audit/block12/replay_verify.py
lake env lean audit/block12/FormalChecks.lean
lake env lean audit/block12/StrataChecks.lean
lake env lean audit/block12/GlobalBoundaryChecks.lean
python3 audit/block12/check_run12_models.py
```

replayは元verifierからroot/outputの解決と説明だけを変更し、同じ宣言一覧のコピーを利用する。
fixtureのoleanも同じソースから生成するため、先にreplayを実行する。
機械可読の判定は[review.json](review.json)、最終checkoutの確認は[prepush.json](prepush.json)。
