# Lean Block01–12 / Run13証明済み部分の監査引継ぎ

2026年11月10日（JST）。このスナップショットは `work` ブランチで公開する。

## 最新：Run13は部分到達、指定完成条件は未達

Run12 `6b8d168` を基準に、actual最小表示・実変数Koszul・有限自由解消・通常Tor比較・k有限homologyを追加。
通常Tor比較はobjectwiseで、graded/極小解消rank/actual L[X] base change/有界比較等は未完。
X_BASIC・I_FIELD全体を閉鎖済みとは数えない。

入口：[Run13検証と範囲](verification/block13/README_JA.md)、
[未完宣言](docs/RUN13_REMAINING_DECLARATIONS_JA.md)、
[20run再校正](docs/RUN13_20RUN_RECALIBRATION_JA.md)、
[宣言全一覧](verification/block13/declarations.json)。
`verification/block13/verification.json` のPASSは証明済みexportのコンパイル・回帰・公理検査のみを意味する。
過去のBlock01–12検証原本は保持した。

## 最初に読むもの

1. [現在のLean化進捗](LEAN_PROGRESS.md)
2. [Block01：small scalar](NSP14/Ordinary/SmallScalar.lean)
3. [Block02：Sidon・数値Apéry・scalar接続](NSP14/Combinatorics/Sidon.lean)
4. [Block01の範囲](verification/block01/README_JA.md) と [Block02の範囲](verification/block02/README_JA.md)
5. [V03骨子](proof_structure_v3/P14_PROOF_SKELETON_V03_JA.md) と [依存表](proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)
6. [Block03：資源からSO3](NSP14/Ordinary/Resources.lean) と [式の対応・範囲](verification/block03/README_JA.md)
7. [Block04：rank 2・3の全行数値評価](NSP14/Ordinary/LowRank.lean) と [重み表・範囲](verification/block04/README_JA.md)
8. [Block05：調和和障壁・全大rank基点](NSP14/Ordinary/LargeSeed.lean) と [原稿対応・範囲](verification/block05/README_JA.md)
9. [Leanと最終原稿の対応・変更台帳](docs/LEAN_PAPER_ALIGNMENT_JA.md)
10. [Block06：大rank scalar全域閉鎖](NSP14/Ordinary/LargeScalar.lean) と [有理数シフト・範囲](verification/block06/README_JA.md)
11. [Block07：ordinary数値全域・全行統合](NSP14/Ordinary/NumericalClosure.lean) と [3証明単位・入力・範囲](verification/block07/README_JA.md)
12. [Block08：実半群・Apéry・order・数値head](NSP14/Semigroup/Basic.lean) と [6ファイル・範囲](verification/block08/README_JA.md)

13. [Block09：半群環の実冪・次数付き商・積](NSP14/Semigroup/IdealPowers.lean) と [7ファイル・範囲](verification/block09/README_JA.md)

14. [Block10：全次数付き環・actual核/head商](NSP14/Semigroup/KernelHead.lean) と [7ファイル・範囲](verification/block10/README_JA.md)

15. [Block11：actual斉次N・QとApéry/Hilbert](NSP14/Semigroup/NonAperyIdeal.lean) と [12ファイル・範囲](verification/block11/README_JA.md)

16. [Run12：actual同jump S₀加群同型・全terminal上限・完備接錐比較](verification/block12/README_JA.md) と [原稿対応A23–A27](docs/LEAN_PAPER_ALIGNMENT_JA.md)

## 特に確認してほしい境界

- `gap_shift` は任意の有理数シフト `s,t : ℚ` の恒等式。
  `small_gap_pos` の正値性は `4 ≤ r ≤ 8`、非負整数シフト `s,t : ℕ`、
  および `r ≤ 5 ∨ s+t ≠ 0` の下で成立する。
- rank6–8の悪い角ではgapが負になることもテストしている。
- Sidon性は同じ項の反復を含む二項和の一意性。差の単射は合成数・偶数のmodulusを許す。
- `AperyPairData` は加法部分モノイドの数値最小元・二項和の最小性・和の一意性を明示した入力。
  actual Q₂の最大性からこのデータを構成する代数的な橋は未実装。
- 境界版のSidon証拠はr≥6かつs=0だけで要求する。内部点へ不要な仮定を加えない。
- Block03は同じ資源列の条件からSO3を証明する。台をcutoff以下に制限しない。
- Block04はrank 2に三角数下限やhead cap M−3を課さない。δ=0を含む。
  rank 3では線形head cap H₁≤3δを明示して要求し、top行も評価する。
- Block05は全r≥9の基点正値性。任意のδ・eへの延長を済ませたとは扱わない。
  原稿から短縮した増分比較は変更台帳A05の証明と照合する。
- Block06でその基点を有理数e≥10・δ≥a_rまで延長した。
  t(t−1)の非負性を有理数へ誤用せず、b₀−(1−α)/2>0を使う。変更台帳A06参照。
- Block07では具体的target余裕も二項係数から証明し、全cut rank・全行の数値比較へ統合した。
  同じ資源の条件と境界証拠は入力。actual Torやtarget Betti公式を構成したとは扱わない。
- Block08は実半群からm/e・最小生成系・order・Apéry数値座標を構成する。
  数値terminal/headの全単射をactual T/Nの加群同型と混同しない。接錐との環同定は後続。
- Block09で代数的半群環の実冪・各次数の有限単項式基底・商上の積とterminal単項式の核判定を構成した。
  その先の全直和と核/商基底の接続は、Block10で以下の範囲まで進めた。
- Block10は全直和を可換k代数へ構成し、actual x乗算の核全体・像全体・principal quotient Aの基底まで同定する。
  その段階のN/Q接続はBlock11で以下の範囲まで進めた。global T≅Nは主張しない。
- Block11はactual斉次N、実商Q、Apéry基底、actual次数像・Hilbert関数、自然なA₂→Q₂の同型、標準生成・Artin性、最高次数νまでを構成する。
  完備化比較・同jump strata・jump上限はRun12で下記の範囲まで閉じた。A・N・T全体の有限性、actual資源とTorは後続。
- Run12はactual非x原子S₀の全作用とA/Q全射、反対向きの実斉次部分加群、actual同jump商のS₀線型同型と同じ写像の次数差sを証明する。
  `terminalHeadVectorEquiv`はk線型座標同値のみ。S₀線型性を主張するのは`jumpStratumEquiv`であり、全体T≅Nではない。
  すべてのterminalで2≤jump≤νを直接証明し、δ=0でactual T=N=0も示す。
- literal k[[S]]の実極大イデアル冪の接錐と代数的Gの次数付きk代数同値がRun12で閉じる。
  単項式・x・核・G→A→Qも自然に運ぶ。`formalOrderIdeal_eq_pow`は無限級数にも実冪判定を証明しており、完備化比較を仮定しない。
- Run12の指定数学目標に未完はない。実際の安定化・towerからの共通資源列、Koszul/Tor/Betti、P14全体は未完成。

## 再現

Lean `v4.36.0-rc2` とmathlib revisionはtoolchain・Lake manifestに固定してある。
標準のelanを利用できる環境で、リポジトリrootから実行する。

```sh
lake build
python3 scripts/verify_block12.py
```

Run12の検証は22ソース再検査・6試験・全宣言監査・計画検査・旧11Block回帰・2監査の44コマンド。
全新規224core宣言・74fixture宣言と旧443件、計741公理依存報告を検査する。
旧41ソース・11テスト・固定環境3ファイルの55hashをBlock11のmanifestと照合する。
通常のLean基盤 `propext`, `Classical.choice`, `Quot.sound` 以外の依存を拒否する。
追加の数学公理や `sorryAx` への依存は認めない。

mathlibキャッシュ先へのアクセスが制限される環境では、初回のみ次で依存を取得し、ソースビルドする。

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
```

このクラウドでは公式GitHub配布の固定Leanを `/tmp/ns-p14-lean` に導入した。
同じ環境なら次で実行できる。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block12.py
```

[保存済みRun12検証記録](verification/block12/verification.json) とログを同梱する。
ローカルで再検証すると所要秒などは更新されるため、厳密な比較対象には監査するコミットを指定する。

[Block01の独立監査](audit/README_JA.md) と [今回の対応記録](docs/BLOCK01_AUDIT_RESPONSE_JA.md) を保存した。
`audit/` と既存ZIPは監査時の記録、`verification/block01/`・`block02/` はBlock01監査修正までの記録。
Block03–10の記録も保持する。今回の公開import追加後の照合対象は `verification/block12/MANIFEST_SHA256.json` とする。

[Block02独立監査](audit/block02/README_JA.md) は条件付き数値ブロックとして合格。
Block03についての上記記載は旧観測時点。今回は最新のBlock10外部監査branch `audit/block10-20261110`（28300b47f72df87983c3e1dba10a11da3466032d）の合格を確認した。認証範囲は代数的G/T/A。
Run12の独立実装レビューは[別記録](verification/block12/INDEPENDENT_REVIEW_JA.md)であり、監査スレの最終数学査読とは区別する。

## 同梱資料

V03、旧証明、二つの紙上置換、Navi別証明、Lean化計画、対応ZIPを保存している。
旧資料があることは現Lean証明の依存にそれらを公理として足すことを意味しない。
コンパイラ本体、`.lake`、生成された`.olean`、Pythonキャッシュ、接続設定や資格情報は含めない。
V03骨子ビルダーの入力指定文は元の添付パスを参照する。必要なら同梱V03 ZIPから元の相対位置へ復元する。
Leanのbuild・検証はその添付指定文に依存しない。
