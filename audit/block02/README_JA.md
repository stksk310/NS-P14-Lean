# Block02 独立監査

2026年11月9日（JST）。判定：**条件付きの組合せ・数値ブロックとして合格。Block02に修正を要する数学的欠陥は見つからなかった。**

対象は `stksk310/NS-P14-Lean` のコミット
`324415fb77ba6cdca99113ec19fdc5b4e9c1919b` にある
`NSP14/Combinatorics/Sidon.lean`。実装は `f11c372` で追加された。
監査中の別ブロックの修正と区別するため、このコミットに固定した。

## 再検証

- Block02 manifestの19件すべてが一致。
- 同梱Block02 ZIPの20ファイルすべてが対象コミットと一致。
- 固定した9依存のコミットが一致し、追跡対象のソースに変更はない。
- Lean v4.36.0-rc2、指定のmathlibで再ビルド・新ソースの再検査・Block02テスト・Block01回帰テストがすべて終了コード0。
- Block02の14定理とBlock01の10定理の公理依存は保存ログと一致。`propext`・`Classical.choice`・`Quot.sound` の範囲内で、`sorryAx`・追加の数学的公理への依存はない。
- Block01の証明ソースは元のハッシュと一致。

今回のビルドは、Block01監査でソースから構築済みの同じ固定依存を再利用し、追加の依存とBlock02を構築した。ビルド全体のターゲット数は2526ジョブ。

## 数学的な確認

`IsSidon` は反復項を含む二項和の一意性を表す。
相異なる2点の順序付き差を非零剰余へ単射にする証明は、偶数・合成数の法にも適用できる。
正整数の法は `[NeZero m]` で要求されている。

数値Apéry最小元の一意性から、同じ剰余を持つ最小元の数値的一致を導く手順は正しい。
`AperyPairData` の `pair_min` と `pair_unique` を用いたSidon構成、および
`m ≥ e(e−1)+1` と `d ≥ (e−1)²` の導出は、明示した仮定の下で紙上証明SO1の数え上げと一致する。

SO2のうちBlock01に必要な3つの角は、次の濃度矛盾で排除される。

| rank | m | e | 非対角順序対 e(e−1) | 非零剰余 m−1 |
|---|---|---|---|---|
| 6 | 28 | 7 | 42 | 27 |
| 7 | 36 | 8 | 56 | 35 |
| 8 | 45 | 9 | 72 | 44 |

境界版は `r ≥ 6` かつ `s=0` の場合にSidon証拠を要求する。`t` は任意。
`s>0` の内部点とrank 4・5では、この証拠を使わずBlock01へ接続できる。

## 追加検査

[AssumptionChecks.lean](AssumptionChecks.lean) は警告なしでコンパイルした。

- 実際の部分モノイド `S=⟨3,4⟩`、法3、値0と4から非自明な `AperyPairData` を構成した。二項和0・4・8はすべて各剰余の最小元であり、反復項も含む。このデータではSidon性が成立し、multiplicity・deficitの下界も等号を満たす。
- 法1のsingleton Sidon集合を確認した。
- rank 4〜8で、modulusの式に現れる自然数の三角数除算と、gapに現れる有理数の三角数が一致することを確認した。
- `pair_min` を外すと、法2の値0・1が反例になる。各値は最小元で数値的二項和も一意だが、`1+1` が `0+0` と同じ剰余になる。
- `pair_unique` を外すと、法5の値0・1・2が反例になる。すべての二項和は最小元でも、`0+2=1+1` が残る。

独立したPython実装では、法1〜14の全32,766部分集合を検査し、強いSidon性と非対角差の単射が一致し、Sidon集合が濃度上界を満たすことを確認した。
この有限検査は補助検査であり、普遍証明はLeanの定理による。

## 合格範囲と残る接続

`AperyPairData` のフィールドは実質的な局所仮定である。
型だけでは `m` がSの実際のmultiplicityであることや、`e` が埋込次元であることは保証されない。
最大のactual Q₂から、0と非m原子を用いてこのデータを構成する代数的な橋は未実装。
次数をまたぐ衝突の排除も、その構成で証明する必要がある。

`scalar_lt_of_boundary_sidon` は依然として `F ≤ upper …` を入力に取る。
actualパラメータの自然数シフトへの表示、SO3資源上界、Tor/Bettiへの移行、
O_SIDON・M10・M12・P14全体は今回の合格範囲に含まない。
これらが未完成という提出側の範囲説明は、コードの仮定と一致する。

## 再現と記録

固定版のLean/Lakeと依存を用意し、リポジトリrootで実行する。

```sh
lake build
lake env lean NSP14/Combinatorics/Sidon.lean
lake env lean tests/Sidon.lean
lake env lean tests/SmallScalar.lean
lake env lean audit/block02/AssumptionChecks.lean
python3 audit/block02/finite_check.py
```

[監査結果](review.json)／[再検証コマンドと終了コード](replay.json)／[公理依存の照合](axiom_check.json)／[ハッシュ照合](hash_check.json)／[依存コミット](dependency_revisions.json)／[追加Lean検査](assumption_check.json)／[有限検査結果](finite_check.json)

[ビルドログ](build.log)／[ソース再検査ログ](source_recheck.log)／[Block02テストと公理ログ](tests_and_axioms.log)／[Block01回帰ログ](block01_regression.log)／[追加Lean検査ログ](assumption_checks.log)
