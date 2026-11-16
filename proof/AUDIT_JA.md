# NS P14 単一証明の検証境界

対象は [単一証明本文](NS_P14_SINGLE_PROOF_JA.md)。2026年11月9日。

**数学的な組立ては、明記した境界補題を採用すれば閉じる。今回の成果を、全祖先の独立再証明、自己完結した完全証明、Leanによる形式検証の完了とは扱わない。**

## 今回の変更とその根拠

| 項目 | 根拠と扱い |
|---|---|
| \(H_1\le m-1-a\) | 元資料の厳密な等式 \(H_1=\delta-a+\ell\) と \(\ell\le e-1\) の直接の帰結。新しいsource仮定を加えていない。 |
| cutの大きさ | \(r=\max(2,p(a))\) を使用。full-ring strataと塔の証明は2本でも成立する。Greenで得た形式を必要なら2本へ拡張する。 |
| 2本・3本のcut | 塔の同じ重みと \(H_1\le r\delta\) から本文第9節で直接評価。元資料のuniversal r2/r3や別top-rank定理を呼ばない。 |
| \(e\ge13\) のscalar | \(H_1\) の強い上界をcutoff式へ代入。数値包絡の単調性を本文で証明し、200個の初期差と傾きを新たに有理数検算した。元R57がこの境界を既に証明していたとはしない。 |
| 全rank | 同じcut・同じ \(H_t\) 列への重み比較を使用。top rankも含める。 |
| 最終被覆 | 正規化幅 \(u<m\) をWと7生成元以下のBで処理し、\(u\ge m\) のordinary側は12生成元以下のBと本文で処理する。歴史的な全gateの和集合を使わない。 |

## 継承した二つの境界

### B 小生成元数

任意体・実際のcompletionについての \(e\le12\) 閉鎖を採用する。直接の上端は現行再構成版R39であり、\(e\le10\) はR38以前の祖先を継承する。

- [R39主定理](sources/R39/R39_MAIN_THEOREM.md)
- [11生成元の組立て](sources/R39/R39_ELEVEN_GENERATOR_PROOF.md)
- [12生成元のordinary側](sources/R39/R39_TWELVE_VARIABLE_LEX_PROOF.md)

例えば12生成元のordinary側だけでも、無限重複度tailへの還元、2,562個のfirst-hit profile、raw lexの不足を埋める欠損2構造定理を使う。元資料には原証明・コード・復元索引がある。**今回は、それらすべての完全再実行および祖先の各証明行の独立再査読をしていない。**

これは「原資料がない」「反例を発見した」「補題が未証明と判明した」という意味ではない。今回の完全性判定で、なお継承している箇所という意味である。旧R39の喪失版と現行再構成版の同一性も主張しない。

### W 幅側

\(e\ge8,u<m\) のR40-WALLを採用する。

- [WALL全域証明](sources/R40/R40_UNIVERSAL_WIDTH_ALL.md)
- [実sourceへの端点移行](sources/R39/R39_ACTUAL_SOURCE_CORE_TRANSFER.md)
- [一欠落幅](sources/R40/R40_UNIVERSAL_ONE_GAP.md)
- [無限幅tail](sources/R39/R39_UNIVERSAL_WIDTH_TAIL.md)

実効target幅は \(\min(du,m-1)\ge u\)。\(u\) を新しい物理幅としてcompletionを取り替えない。WALLの主証明は数式による無限量化の証明であり、有限core標本の外挿ではない。今回はこの接続と中心式を読解したが、そのすべての補助定理・古典入力を形式化してはいない。

本文の最終分割は「\(u<m\) なら \(e\le7\) をB、\(e\ge8\) をW、\(u\ge m\) なら \(e\le12\) をB、それ以上を本文」という順序にした。これでBの11・12生成元の**有限幅core campaign**は使用箇所から外れる。ただしBの \(m\le u\) のordinary側と7生成元以下の全target側を残す必要がある。物理幅が広くても正規化幅が狭いsourceはWで処理する。

## 公刊入力と独自構造補題

| 入力 | 使用する範囲 |
|---|---|
| Elias, *On the deep structure of the blowing-up of curve singularities*, Thm 3.3(i), [DOI](https://doi.org/10.1017/S0305004101005217) | 1次元equicharacteristic CM局所環のmicroinvariants \(L_\rho\le m-e+1\)。本文でfirst neighborhood ringとの同定を明示する。 |
| Greenの超平面制限定理 | 無限体上の多項式環の次数2。有限体では同じ標数の純超越拡大を介する。[Caviglia–Kummini Discussion 2.4](https://arxiv.org/abs/1210.5562) が添付資料の参照。 |
| Peeva, *Consecutive cancellations in Betti numbers*, Thm 1.1, [DOI](https://doi.org/10.1090/S0002-9939-04-07517-3) | 同一Hilbert関数のlex表からの連続消去。Betti数の成分ごとの大小だけで交代rankを比較しない。 |
| Eliahou–Kervaire, *Minimal resolutions of some monomial ideals*, [DOI](https://doi.org/10.1016/0021-8693(90)90237-I) | stable/lex単項式イデアルのBetti公式。 |

公刊定理もLeanでは証明または正確なライブラリ定理との接続を要する。本文は古典全体の独立再証明ではない。jump filtration、strata、tower、剰余占有、rank移行は本文で再構成した。採用した原文22ファイルとハッシュは [SOURCE_INDEX.json](SOURCE_INDEX.json) に固定してある。

## 外した枝

本文の最終組立ては、R41〜R48の生成元数境界の拡大、D16の225,458 DP状態、E273の6,592組、HEAD20、defect57、全source-specific gateのregistryを呼ばない。

R54 all-narrow別証明、R55のpruning/socle fusion、dense witness族、characteristic torsionの診断例、独立のtop-rank閉鎖、4,086本の補助waterfill証明も最終組立てから外す。原資料を改変・削除したわけではない。

既知のwaterfill一般文の符号不足は [原正誤表](sources/core/ERRATA_AND_SCOPE_NOTES.md) の通りである。本稿はその一般文を使わず、正の重みを持つ明示的なcutoff上界を直接証明するので、この補正に依存しない。

## 今回実行した検証

実行結果の詳細は [verification.json](verification.json) に記録する。

1. 元handoffの保存byte検証：manifest 302ファイル、5,605 original objects、27のR57直接anchor、164 semantic recordsを確認。これは数学の証明ではない。
2. 新しい \(e=13\) 境界：\(10\le\delta\le209\) の200行で、初期差と傾きがすべて正。\(\mathcal H_{210}<6\) も有理数で確認。
3. 別の差の恒等式から200行を再計算するcheckerを実行。producer関数はimportしない。
4. 2,040個のrank包絡比較、19,437個のtarget恒等式・下界を有限診断として確認。普遍性の根拠は本文の恒等式・単調性・帰納法に置く。
5. 採用原文22ファイルのSHA-256を再照合。

再実行はリポジトリ直下で次の通り。

```sh
python -B proof/checks/verify_scalar.py
python -B proof/checks/recheck_rows.py
```

Pythonを実行することと、Leanカーネルが有理数命題を証明することは異なる。Leanファイル・toolchainはまだ作っていない。

## 現時点で言えること

本文に残した仮定・量化範囲を保てば、最終組立てに空いたパラメータ領域はない。大きな生成元数側は、同一source・同一field・同一cut・同一targetのまま閉じる。今回の再構成で、P14本体を破る反例や中心鎖の致命的な矛盾は確認していない。

一方、「今回、P14の全証明を一から無条件に検証し終えた」とは言えない。残っている主要作業は、Bの必要部分とWを全依存込みで独立に確認し、上記公刊入力および本文をLeanへ接続することである。現時点の正確な表現は、**明示した境界補題に依存する、一つに整理された計算支援証明**である。
