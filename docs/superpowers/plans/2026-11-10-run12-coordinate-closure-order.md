# 実行スレへの次run指令：Run12 / O_COORDの残りと完備化比較

Block11の完成・検証・Pushを済ませた後、この指令を同じ実行スレで実行する。
すでにBlock11で本指令の一部を証明していれば、その宣言を再利用して残りへ進む。

## 今回の目標とrunの区切り

**全体20 runを目標に、今回は長い1 runで「actualな同jump加群同型・全terminalのjump上限・完備化との比較」まで閉じる。**
小補題・ファイル・内部コミットごとに終了せず、必要な補題、修正、接続、検証、原稿台帳、監査用ZIP、通常のPushまでまとめて進める。
30〜60分は従来の目安であり上限ではない。context圧縮後も同じ目標を継続する。
この指令は追加エージェントやモデルの変更を要求しない。実行スレの既存の実行方法とユーザー指定を維持する。

全体計画：[2026-11-10-p14-20-run-roadmap.md](2026-11-10-p14-20-run-roadmap.md)。
監査済みの基準はBlock10 `791a2c94eda09479d0582f30726669c6d28fbc7b`。
着手時に実際のBlock11 commitとその検証状況を記録する。Block11は観測時点では実行中なので、本指令はその完了を認証しない。

## 最初に読む範囲

- V02 §2とV03 II.1 `O_COORD`、同じ定義で使う§3/II.2の安定化との境界。
- `NSP14/Semigroup/Heads.lean`の数値terminal/head・jump単調性。
- `KernelHead.lean`、`KernelHeadBasis.lean`のactual G・T・Aと次数別作用。
- Block11のactual N、Q、継承された次数、標準生成、νとA₂→Q₂の宣言。
- 最新の監査結果、`docs/LEAN_PAPER_ALIGNMENT_JA.md`、固定環境とGit運用。

## Task 1：actual多項式作用と次数の整合性

**Consume:** Block10の`TangentAlgebra`、`xMultiply`、`HeadAlgebra`とBlock11のactual N/Q・継承次数。

**Produce:** 非xのactual原子で添字付けた多項式環S₀、そのG/T/A/N/Qへの整合する作用、S₀→AとS₀→Qの次数1生成に基づく全射。
S₀→Gは作用を与える準同型であり、全射は要求しない。Gの全射表示が必要な場合はx変数も含む多項式環を使う。

- [ ] `NSP14/Semigroup/PolynomialAction.lean`等、責務を分けたソースへ構成する。名称は既存Block11のAPIと照合して確定し、重複定義を避ける。
- [ ] 変数をactual非x原子の初期単項式へ送る環/代数準同型を定義する。TはGでの核、NはAの実イデアルとして同じS₀の作用を受ける。
- [ ] 作用を数値モデルの都合で定義して済ませず、actual乗算・商写像・次数別単項式基底との一致を証明する。
- [ ] 原子・基底の任意の有限和、次数0、m=1、e=2、任意標数で必要な境界をコンパイル確認する。

## Task 2：反対向きのjump filtrationと同jump加群同型

**Consume:** actual S₀作用、数値ラベルのterminal/head対応、live作用のjump単調性。

**Produce:** `D_s T`（jump≥s）と`F_s N`（jump≤s）のactual斉次S₀部分加群、および
`D_s T / D_(s+1) T ≃ F_s N / F_(s−1) N`のS₀線型同型。
次数pのterminalが次数p+sのheadへ移ることを同じ写像で証明する。

- [ ] `JumpFiltration.lean`等で、ラベル集合だけでなくactual部分加群を構成する。
- [ ] 各filtrationの作用による安定性と包含を証明する。
- [ ] `JumpStrata.lean`等で、terminal→headの写像を商へ降ろし、逆写像・S₀線型性・次数差sを証明する。
- [ ] 2≤s≤νで必要な同型を得る。ベクトル空間同値だけで完成とはせず、全体T≅Nを導かない。
- [ ] 非零stratum、境界s=2/s=ν、異jumpへ移る項が対応するstratum商で消える場合を検査する。適切な具体例の成立条件はLeanで確認する。

## Task 3：全terminalに対する2≤jump≤ν

**Consume:** actual Qの最高次数ν、actual Aの標準生成、N=A内の実イデアル、Task 1–2。

**Produce:** 任意のactual terminal τに対する`2 ≤ jump τ ∧ jump τ ≤ ν`。

- [ ] `JumpBounds.lean`等で、原稿の多項式表示I_A⊆I_Q、I_Qの次数ν+1以下での生成、Nへの移行を証明するか、同じ結論を持つ短いactual証明へ置き換える。
- [ ] 最小headだけの上限から全head/terminalへ上限が伝播することを証明する。上限をデータの仮定に置かない。
- [ ] δ=0などからN=T=0が従う必要な退化境界も接続する。使う生成性・有限性を明示し、未証明の一般Gröbner結果へ隠さない。
- [ ] 代替証明を使う場合は原稿対応台帳へ元の論証と変更点を記録する。

## Task 4：代数的半群環と完備半群環の接錐を接続

**Consume:** actual k[S]と正元イデアル𝔪、実冪の商としてのG、必要な完成環の定義と比較API。

**Produce:** 原稿のk[[S]]の極大イデアルを用いたassociated gradedと、既存Gの次数付きk代数同値。
自然な単項式・x・G→A→Qの対応を追える形にする。

- [ ] `CompletedComparison.lean`等でk[[S]]の定義を明記する。m-adic completionを採用する場合は、原稿の形式級数モデルとの同定又は同値な定義として使える証明を供給する。
- [ ] 各次数の冪の商の同値を、乗法・単位元・kスカラー作用・次数を保つ全体の同値へ組み立てる。
- [ ] xが[t^m]へ、単項式が同じ指数の初期形式へ対応し、実核/商を運べることを証明する。
- [ ] ℕとjumpのある実半群で、自然写像と積の対応を確認する。完成環を定義しただけ、線型同値だけ、比較を仮定した条件付き定理だけではこのTaskを完了扱いしない。

## Task 5：検証・監査引継ぎ・Push

- [ ] `tests/JumpStrata.lean`、`tests/CompletedComparison.lean`等で上記の受入条件を検査する。proof-bearing定義・同値・構造instanceも全て公理依存検査に含める。
- [ ] 全新規ソース、必要な既存全Block回帰、過去の監査境界、固定依存と前Blockのhashを検査する。実行したものと未実行のものを区別する。
- [ ] 台帳・進捗・検証入口を更新し、`verification/block12/`と監査用ZIPを作る。Block11完了後の命名に合わせて関連ファイル名は確定する。
- [ ] 通常のcommit/Push後にリモートSHAとclean worktreeを確認する。監査スレが追える宣言一覧・入力・未完一覧を残す。

## 終了条件

本runの完了条件はTask 1–4のactual接続とTask 5の検証・公開が閉じたこと。
純粋な数値対応だけでactual O_COORD全体を完成と報告しない。
必要な基礎exportが足りなければ同じrunで補う。解けない数学的障害や実際の実行制約が出た場合は、閉じた定理と未完の正確な宣言・理由・依存を保存し、20 run計画の配分を更新する。
予定run数に合わせて`sorry`・追加数学公理・未証明引数・scope縮小で完了を作らない。

完了報告には「O_COORDの閉鎖状況、完成環との比較の閉鎖状況、Run13へ渡すactual export、未完の有無、検証、branch/commit」を含める。
