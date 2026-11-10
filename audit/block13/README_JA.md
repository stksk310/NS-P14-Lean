# Run13 独立監査：actual Koszul・通常Tor・graded Betti・体拡大

2026年11月10日（JST）。対象：`stksk310/NS-P14-Lean`。
対象コミット：`d8556dc615b1e1633379f4567e9e795b3f1c8ae3`。
Run12基準：`6b8d16889ea9b4d88567f0d9ac70391db2a49824`。
途中版`92cbe8f`とPARTIAL ZIPではなく、最終継続版を監査した。

**判定：証明部分は指定されたRun13共通基盤として合格。検証の再現手順にP2を1件指摘し、修正が必要。**
証明・定理の型について新たな修正必須の欠陥は見つからなかった。
提出スクリプトはクリーンな試験ビルドで停止したが、依存順と試験用mathlib依存の準備を直した監査用コピーでは全40検査が通過した。
修正パッチも同梱する。提出ソース・検証原本・ZIPは変更していない。
資料内の実行指示は監査対象として読み、ユーザーの監査依頼と区別した。

## 修正事項：P2 / 最終検証が未記録の試験キャッシュに依存する

対象：[scripts/verify_run13_continuation.py](../../scripts/verify_run13_continuation.py:40)。
`newtests`は名前順に並び、最初が`tests/ActualGradedBaseChange.lean`、
共通fixtureの`tests/Run13Fixtures.lean`は後になる。
最初の試験はそのfixtureをimportするため、試験の`.olean`がない状態では停止する。
通常の`lake build`のdefault targetはNSP14のみで、testsはビルドしない。

隔離スナップショットでライブラリbuild、旧11Block、Run12の6試験、公理検査の計19コマンドが成功した後、
20番目で次のエラーを再現した。

```text
tests/ActualGradedBaseChange.lean:1:0: error: object file
'.../.lake/build/lib/lean/tests/Run13Fixtures.olean'
of module tests.Run13Fixtures does not exist
```

[失敗ログ](as_submitted/ActualGradedBaseChange.log)・[実行結果](as_submitted/result.json)・
[提出手順の監査用コピー](replay_verify.py)を保存した。
`verification/block13_continuation/README_JA.md`の単独実行手順では、このfixtureの先行コンパイルを指示していない。
以前のPARTIAL用スクリプトも最終版の新規ファイル集合を拒否するため、最終版の前処理としてそのまま使えない。

加えて、このfixtureが追加するmathlibの`Mathlib.Algebra.Field.ZMod`と
`Mathlib.FieldTheory.RatFunc.Basic`もdefault library buildの依存閉包には入らない。
mathlib全体のキャッシュを取得済みなら外部依存は揃うが、試験fixture自体の順序問題は残る。

対処は[verification_order_fix.patch](verification_order_fix.patch)。
build対象に試験用mathlibの2 moduleを含め、Run13Fixturesを最初にコンパイルする。
ライブラリや数学的主張は変えない。
`git apply --check`成功、修正相当の[再検証](replay/verification.json)40/40成功、警告なし。
この監査branchでは提案パッチとして保持しており、元の検証スクリプトには適用していない。
実行スレで適用・再検証し、検証完了記録を更新してほしい。

## 独立再検証と整合性

- 固定公式Lean `4.36.0-rc2`、commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`を使用。
  mathlibは`139105d28c7685a154cb3093f79edb2e16708099`。
  新しいローカルbuild領域でNSP14をビルドし、共有した依存キャッシュについても9リポジトリのrevisionと追跡ソースのclean状態を確認した。
- 新規coreは69ファイル・5,895行。新規受入は17ファイル。
  修正した順序で全受入、旧Block01–12、公理検査、計画検査、過去2境界監査まで40コマンドが成功した。
  [replay_fixed_verify.py](replay_fixed_verify.py)の元スクリプトとの差は、提案パッチ・root/outputパス・説明文のみ。
- Lean環境から1,284宣言（core 1,207、受入77。自動生成宣言を含む）を取得。
  全件の名前・所属module・export種別・通常型・explicit型・公理依存が提出記録と一致した。
  旧741件の公理依存報告も再検査した。
  依存は`propext`・`Classical.choice`・`Quot.sound`の部分集合で、追加数学公理・`sorryAx`なし。
- proof erasureでimport時の種別が`axiomInfo`となる証明は、Leanの`collectAxioms`で検査した。
  [負の対照試験](check_axiom_detector.py)では、一時ディレクトリだけに生成した実公理とそれに依存する定理の両方が拒否され、
  通常の証明が許容されることを確認した。対照moduleはNSP14にも受入試験にもimportしていない。
- 69ソースと17受入に`sorry`・`admit`・`unsafe`・`native_decide`・外部実装差替え等なし。
  [独立照合結果](replay_comparison.json)はclosure JSONの真偽を証明の代わりに使っていない。
- 最終source hash92件、旧証明・試験・固定環境84件が対象commitと一致。
  COMPLETE ZIPは634メンバー、内部manifest633件についてhash・ファイル本体・gitの3者が一致。
  ZIP SHA256は`2c8e436a7f917fc6de068619441a0cbe80d3f9188b5e86e83aa70a35e4276573`。
  [integrity.json](integrity.json)に全依存revisionも保存した。

## 数学的な主要接続と適用条件

| 対象 | 確認した内容 |
|---|---|
| 最小表示 | 全actual原子のe変数からGへの次数付き全射と次数1の線型独立性。既存S₀のe−1変数や将来のcut変数と区別している。 |
| 実Koszul | actual変数乗算のconeを反復する。微分は`(-d, X· + d)`の符号付きブロックで、任意のsquare-zero mapを入力にする構成ではない。H₀は実変数作用で生成する部分加群による商。上端の消滅はIsZeroから証明する。 |
| 通常Tor | 相異なる多項式変数について正次数exactness、augmentationのquasi-isomorphism、実自由解消を構成。tensorした複体を同定し、mathlibの`CategoryTheory.Tor_i(M,k)`へ接続する。左右の規約は第2因子kを解消するもの。自然性も同じ写像について証明する。 |
| 有限性 | 有限P生成・Noetherian性からP上のhomology有限生成を得る。変数のnull-homotopyとaugmentationへの作用還元から有限k次元を導く。一般のGやそのchainを有限k次元とは仮定しない。TのS₀有限生成にはxによる消滅と変数削除を使う。 |
| graded/total | 内部次数は係数次数+i。実際のdegree subcomplex、その全直和と元の複体の同型、無限直和のexactnessからhomology分解を得る。有限homologyから次数台の有限性とtotal=有限和を導く。 |
| 完全列 | 実短完全列からKoszul短完全列とconnecting mapを構成。正次数では両側のconnecting rank、次数0ではincoming rankだけを含む次元式を証明する。商のBetti単調性は使わない。 |
| 極小解消 | `MinimalFreeTower`は実自由基底・syzygy短完全列・像が変数倍に入る極小性を入力に持つ。そのデータから実ProjectiveResolutionとBetti=各rankを証明する。任意加群の極小解消の存在を証明したとは扱わない。 |
| rank Euler | 整数値の部分交代和を、全次数でexactな有限次元ベクトル複体のdの像の次元と同定する。非負性・上端0も同じexactnessを使う。これはまだactual Betti列へ局所化を適用した定理ではない。 |
| 有界比較 | 実monic chain mapのcokernel商による有限filtrationのhomology次元上界。中間homologyの有限性も導く。spectral sequenceの退化は仮定しない。 |
| 同標数の体拡大 | 実L⊗ₖP≃L[X]と変数作用、複体・homology・その自然性を接続。G/T/A/N/Qの実座標を使って、拡大先のactual加群へ同定する。五つの独立なactual L側order gradingとのdegree比較と、同じtotal比較へのinclusion可換式まで証明する。形式級数環全体のtensor同型は使わない。 |
| 同jump・完備接錐 | Run12の実多項式線型同型からKoszul/Tor/total Bettiを運ぶ。同jumpのgraded Bettiは正確な次数差+sを保つ。globalなT≅Nは主張しない。 |
| 標準単項式・minor | 全非零ideal元のleading exponentを使う標準指数、除法によるnormal form、実商の基底を構成する。生成元の初項だけで済ませていない。実行列の選択minorと三角・対角±1の条件から任意標数のrank下界を得る。特定harmonic initial idealの証明は含めない。 |

## 追加の境界検査

[BoundaryChecks.lean](BoundaryChecks.lean)の4定理と1例が警告・追加公理なしで通過した。
標数2の通常のderived Torそのものの次元がbinomial値になることを検査し、空変数・次数0も含めた。
残余体2変数の部分交代和はc₁=1、c₂=0。
一方、自由多項式加群ではc₁=−1であることをLeanで証明した。
これはrank 0等の入力を外した非負性を主張できないことの対照であり、ソースの定理への反例ではない。
さらにZMod 2→RatFunc(ZMod 2)で、actual Gのdegree比較が同じtotal比較と可換であることを検査した。

[独立有限計算](check_finite_koszul.py)では、ソースの行列を使わず外積基底と単項式作用から行列を作った。
0〜3変数の27個のdownset商を標数2・3・5・7で検査し、d²=0、homology次元、H₀、socle、Euler和を照合した。
ほかに3乗による完全交差12ケースと非完全交差の具体例を検査した。
GF(2)→GF(4)では、拡大体固有の非零スカラーを使う基底変更も施し、全対象微分のrank保存を確認した。

12短完全列については、Cの実cycleをBへ持ち上げて微分し、Aのboundaryで割ってconnecting rankを計算した。
2変数の例ではβ(A)=β(B)=(1,2,1)、β(C)=(1,3,2)、δ₁・δ₂のrankは1・2。
`βB_i + rank δ_i + rank δ_(i+1) = βA_i + βC_i`が次数0・上端を含めて一致した。
有限実験は一般のLean証明を補うもので、全半群やP14の証明の代用ではない。
[結果](finite_koszul.json)・[ログ](finite_koszul.log)を保存した。

## 後続runへ残るもの

Run13指令はactual cut/tower等の実体化を後続の責務として明示している。
今回の共通基盤はその境界で認証し、`X_BASIC_closed_for_Run13`をP14全体のX_BASIC閉鎖に読み替えない。
特に次は別途必要である。

- actual cut・正則列・offset安定化と体積、共通資源列。
- harmonic initial ideal・ordinary/AP targetの実証明、actual towerと特定connecting rank。
- actual解消等を必要なflat局所化へ運び、rank Eulerへ入るexact有限ベクトル複体とrank 0を供給する接続。
- 端点移行・公刊入力・最終P14の統合。

Block11のP3文書指摘（`verification/block11/README_JA.md:97`の「後者」）は原本に残っている。
これはRun13の新規欠陥ではなく、[以前の修正提案](https://github.com/stksk310/NS-P14-Lean/blob/audit/block11-20261110/audit/block11/README_JA.md)として継続管理する。

## 再現

固定toolchainとlake-manifestの依存を準備し、repository rootで実行する。

```sh
python3 audit/block13/check_integrity.py
python3 audit/block13/replay_fixed_verify.py
lake env lean audit/block13/BoundaryChecks.lean > audit/block13/boundary_checks.log 2>&1
python3 audit/block13/check_axiom_detector.py
python3 audit/block13/check_finite_koszul.py
python3 audit/block13/check_replay.py
```

`check_integrity.py`は比較用git repositoryを`/workspace/NS-P14-Lean`としている。
別の配置ではその定数を変更する。
提出手順の順序不具合を再現する場合は、Run13受入の`.olean`がない別build領域で`replay_verify.py`を使う。
すでに修正手順を実行したキャッシュではfixtureが存在するため、この不具合は隠れる。
