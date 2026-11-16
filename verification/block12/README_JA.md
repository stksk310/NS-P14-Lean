# Run12：actual O_COORD・完備形式級数接錐との比較

日付：2026年11月10日（JST）。branch：`work`。
Block11基準：`a6aac7b345e3e7dbd3ac660468bdd220ecfa7dca`（完成・検証・Push済み）。
ユーザー指定の20run計画とRun12指令に従い、目標1–4の数学的接続を閉じた。

## 受入条件と実証明の対応

| 条件 | actualなLean export | 試験 |
|---|---|---|
| 非x原子の単一S₀・G/T/A/N/Q作用 | `NonXAtom`, `PolynomialRing`, `polynomialToG/A/Q`, `polynomial_smul_G/T/A/N/Q` | `PolynomialAction`：有限和・スカラー・商写像、m=1・e=2 |
| A,Qへの次数1生成・全射 | `polynomialToA_surjective`, `polynomialToQ_surjective`, `polynomialToG/A/Q_X_mem_degree`, `polynomial_X_smul_G/T/A/N/Q_degree` | 任意可換非自明係数環のgeneric例、ℚ・ZMod 2 |
| 反対向きactual斉次S₀部分加群 | `descendingJump`, `ascendingJump`, `_antitone`, `_monotone`, `descendingJump_homogeneous`, `ascendingJump_homogeneous` | 実G/A成分射影と実乗算の安定性 |
| actual同jump商のS₀線型同型 | `jumpStratumEquiv`（0<s；2≤s≤νを含む） | 非零層・s=2・s=ν・異jump項の商での消滅 |
| 同じ同型の実次数差s | `descending/ascendingStratumDegree`（実斉次代表元の商像）, `jumpStratumEquiv_degree` | 任意p・任意商元の所属同値 |
| 全terminalの2≤jump≤ν | `terminal_jump_bounds` | 閾値を仮定しない；ν=2の実例、δ=0でactual T=N=0 |
| literal k[[S]]・実極大イデアル冪 | `formalSeriesAlgebra`, `formalMaximalIdeal_isMaximal`（Field）, `formalOrderIdeal_eq_pow` | 無限形式級数と実冪；一般可換係数環で冪判定 |
| 自然な次数付きk代数比較 | `polynomialToFormal`, `completedPieceEquiv`, `completedGradedAlgEquiv`, `_of`, `_initial`, `_x`, `_xMultiply` | ℕと実jump半群で単項式・積・核の整合 |
| 実核・商の運搬 | `completedKernelEquiv`, `completedHeadAlgEquiv`, `completedAperyAlgEquiv`, `_mk` | G→A→Qの自然な商図式 |

`JumpStrata` の実例S=〈9,10,15,26〉では、τ=26はorder=1・jump=2、τ+15=41はorder=2・jump=3。
15のlive作用はTのjumpを増やし、jump=2の商で0となる。対応するN商でもS₀線型性により0。
数値のorder上限は有限の重み表をLeanのkernelで検査し、全正元表示の長さの上界へ証明付きで接続した。
外部Pythonの数値計算結果を公理や未証明引数として使わない。
S=〈4,5,11〉ではν=2に非零stratumがあり、s=2とs=νの両境界を検査する。
ℚ、ZMod 2、ZMod 4を含む。標数に依存する数学的な仮定を置かない。

## 検証

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block12.py
```

固定Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`。
22新規ソース、127定理を含む224新規core宣言。
74個の名前付きfixture宣言も含めた298新規公理依存報告と旧443報告、計741件を検査。
44コマンド：build・全新規ソースの単独再検査・6新規試験・全宣言axiom監査・20run計画検査・旧11Block回帰・旧2監査。
警告、失敗、`sorryAx`、追加数学公理を拒否する。許容基盤は `propext`, `Classical.choice`, `Quot.sound` のみ。
ソース/試験の新規ファイル集合と、このrunで採用した構文の名前付き宣言（def/abbrev/theorem/instance）を毎回再計算し、登録漏れ・一覧との不一致を拒否する。
将来lemmaや追加修飾子等の構文を導入する際はcollectorも拡張する。現在の全224+74宣言の被覆は独立レビューでも一致を確認済み。
旧41ソース・11試験・固定環境3ファイル、計55hashをBlock11 manifestと照合する。
過去の検証原本は変更しない。`jump_bounds_red.log` は実装前の不成立を示す記録であり、最終検証ログではない。

全新規宣言・入力・所属ソースは `declarations.json`、実行結果は `verification.json` と対応ログ。
数学的な代替証明は [A23–A27](../../docs/LEAN_PAPER_ALIGNMENT_JA.md)、実行経過は [実行台帳](../../docs/RUN12_EXECUTION_LEDGER_JA.md)。
独立実装レビューは [INDEPENDENT_REVIEW_JA.md](INDEPENDENT_REVIEW_JA.md)。これは監査スレによる独立数学査読の代替を意味しない。

## Run13へのactual export・境界

O_COORDの本指令範囲と形式級数接錐の比較に未完宣言・未証明入力はない。
Run13へは実S₀作用、actual A/Qへの全射、実T/Nの斉次jump filtration・商同型・次数差、全terminal上限、自然な完備環比較を渡す。
計画の `X_BASIC` 全体（Koszul/Tor・有限性・体拡大等）の閉鎖を前倒しで主張しない。
A/N/T全体の有限性、安定化、actual資源・cut/tower、最大Q₂からSidonデータ、Tor/Betti・公刊入力・P14全体は後続。
原稿のνをactual Qの最高次数として使う前提はBlock11の実定理で供給済み。
formal側Nは自然なactual商同値で移したイデアルであり、別の未証明モデルとの同定は挿入しない。

## 配布

監査ZIP：`artifacts/NS_P14_LEAN_RUN12_20261110.zip` とSHA256。
`MANIFEST_SHA256.json` は当該ソース・試験・固定依存・原稿・台帳・検証記録をhash化する（自身とZIPを除外）。
ZIPは同manifestとその全entryをroot-relative pathで含む。コンパイラ・.lake・資格情報・生成oleanは含まない。
公開commitは `git rev-parse HEAD` と `git ls-remote origin refs/heads/work` で照合する。
