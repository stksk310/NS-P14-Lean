# 実行スレへの指令：Run13 / actual Koszul–Tor・有限性・体拡大の共通基盤

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun13として、actual多項式加群のKoszul複体を通常のTor/Bettiへ接続し、有限性・完全列・必要なrank比較・体拡大の基盤を一つの長いrunで閉じる。

**Architecture:** 有限な実変数列の具体的Koszul複体を中心に、既存のhomology・完全列・flat base changeを再利用する。actualな接錐・T/A/N/Qへの作用を入口とし、通常のBettiの意味まで証明でつなぐ。汎用理論はP14で使うexportに必要な範囲を実装する。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存検証スクリプト。

**Spec:** [20 run計画](2026-11-10-p14-20-run-roadmap.md)、V03 `X_BASIC`・`I_FIELD`、後続`O_HARMONIC`・`O_TOR`・`E_HOMOLOGY`・`E_TRANSFER`が使う基礎export。

## Global Constraints

- 基準：Run12 `6b8d16889ea9b4d88567f0d9ac70391db2a49824`。実行スレの完成・検証・Push報告を確認済みだが、指令作成時点で監査スレの独立監査は未実施。
- 着手時に最新work、Run12の検証入口・宣言一覧・監査修正の有無を確認する。既存の証明・検証原本を保持し、新しいscopeへ無言で読み替えない。
- 目標は「全体20 run」。小補題・ファイル・途中コミットごとに終了せず、実装・接続・修正・必要な検証・原稿台帳・監査引継ぎ・通常Pushまで同じrunで進める。
- 従来の30〜60分は硬い上限にしない。context圧縮後も継続し、待機で時間を埋めない。実際の実行制約や数学的な障害は正確に報告する。
- 完了の依存は`propext`・`Classical.choice`・`Quot.sound`の範囲。追加数学公理・`sorryAx`・未証明の比較定理で到達点を作らない。
- 公刊入力やactual towerの実体化は後続runの担当。中間の条件付き汎用補題は明記し、その条件が今回どこまで供給されたかを追えるようにする。

## Review Focus

1. Run12の`S.PolynomialRing k`は非x原子のe−1変数S₀。Gのintrinsic Bettiを測る全e変数の最小表示環、および将来のr変数cut環Pと混同しない。
2. Gなどのchain groupはk上無限次元になり得る。homologyの有限性を証明してからfinrankを使い、無限次元でのfinrank=0を消滅証明に使わない。
3. Koszulの符号・augmentation・次数・d²=0は任意標数で成立させる。標数2を別のrank一致の仮定で処理しない。
4. 体拡大は実際のgraded piece・加群・複体の自然写像で扱う。無限形式級数環そのもののテンソル積が常に形式級数環と同型、とは仮定しない。
5. connecting mapと非負補正項の添字を保持する。商のBetti単調性、spectral sequenceの退化、globalなT≅Nは使わない。

---

## Task 1：実変数と最小表示を固定

**Consume:** Run12の`NonXAtom`、`PolynomialRing`、`polynomialToG/A/Q`、actual G/T/A/N/Qと完備接錐比較。

**Produce:** 任意の有限変数集合の多項式環・augmentation・加群作用の共通インターフェース、全actual原子のe変数によるGの最小表示。

- [ ] `NSP14/Homological/Presentation.lean`等、既存の構成と衝突しない責務別ファイルを確定する。以下のファイル名は候補で、既存APIを確認して統一する。
- [ ] 全原子を使う環からactual Gへの次数付き全射と、次数1に余分な線型関係がないことを証明する。sourceとtargetの変数集合は別々に保持する。
- [ ] 既存S₀のT/A/N/Q作用を同じgenericインターフェースへ接続する。S₀→Gの全射性は要求しない。
- [ ] 完備接錐の比較が、対応する多項式作用についても線型であることを示し、後の複体へ運べるようにする。
- [ ] m=1・e=2・空変数集合・次数0で、変数数や環の取り違えがないことをコンパイル検査する。

## Task 2：具体的Koszul複体・homology・自然性

**Consume:** 有限変数集合σ、P=k[Xσ]、実際のP加群M。

**Produce:** Kᵢ(X;M)、実微分d、d²=0、Hᵢ=ker dᵢ / im dᵢ₊₁、加群準同型から誘導されるchain mapとhomology map。

- [ ] `KoszulComplex.lean`・`KoszulHomology.lean`等に、外積基底又は有限部分集合による具体的複体を実装する。dを正しい変数作用の符号付き和とし、単にsquare-zero mapを入力に持つモデルでは済ませない。
- [ ] augmentationとH₀(M)≃M/(Xσ)M、i>|σ|での消滅、graded shiftの規約を証明する。
- [ ] σ=∅、σが1・2変数、残余体k、自由加群P、P/(X²)、標数2でd²=0・homologyを検査する。

## Task 3：通常のTor/Bettiとの実比較

**Consume:** Task 2の複体、P上の通常のtensor/resolution/homology API。

**Produce:** 通常のTorと上記Koszul homologyの自然同型、およびP14で使うBetti数との一致。

- [ ] 多項式変数のKoszul複体がkの実際の有限自由解消であることを証明する。augmentationのexactnessを未証明のfieldや引数に残さない。
- [ ] 解消をMとtensorした複体とTask 2の一致を証明し、Torの変数順・左右の規約を固定する。別のTor規約へ移る場合は、その比較も証明する。
- [ ] `def Tor := KoszulHomology`と名付けて比較をrflで済ませず、既存の通常のTor又は通常の解消による定義へ接続する。
- [ ] 極小自由解消のrankを後で使えるよう、実際の極小解消が与えられた場合にBettiとrankが一致する橋も供給する。解消の存在を使う定理では必要な存在証明も供給する。
- [ ] actual Gと完備接錐比較の両側で、対応する実変数のBettiが一致することをこの同じ比較から得る。
- [ ] Run12の同jump S₀加群同型から誘導されるKoszul/Tor同型も接続する。total Bettiは保存され、graded Bettiでは証明済みの次数差sを保持する。

## Task 4：homologyの有限性・graded/total Betti

**Consume:** 体k、有限変数P、有限生成P加群Mと、必要なgrading・局所有限性。

**Produce:** Tor/Koszul homologyの有限k次元、totalとgraded Bettiの整合性・有限台、actual G/T/A/N/Qへの適用条件。

- [ ] 有限生成性・Noetherian性を用いてhomologyのP有限生成を示し、各変数作用のnull-homotopyからaugmentation idealがhomologyを消すことを証明する。これらから有限k次元を得る。
- [ ] Mそのものの有限k次元は一般仮定にしない。source Gにも適用できる形にする。
- [ ] G/A/Qの有限多項式加群性と、T/Nの必要な有限生成性をactual ideal/submoduleと作用から証明する。TをS₀加群として扱う場合のxによる消滅と変数削除も証明する。
- [ ] i>|σ|のBetti消滅と、graded/totalの有限和の一致を証明する。A/N/Tの有限k次元を、まだ未実装のoffset安定化から仮定しない。

## Task 5：完全列・rank Euler・有界比較

**Consume:** Task 2–4のactual複体と有限homology、既存の完全列・rank-nullity・有限filtered complexの道具。

**Produce:** 短完全列からのhomology/Tor完全列、必要な次元不等式と補正rank、後続O_TOR/E_TRANSFER向けの有界比較。

- [ ] 0→U→V→W→0を各Koszul次数へ運び、実connecting mapを構成する。必要な境界i=0/topも含めて次元式を導く。
- [ ] 部分交代和cⱼとsyzygy/rank Eulerの一致、rank 0での非負性・末端の消滅を、必要な有限自由解消又は十分な証明済み代替から得る。自然数の切捨て減算で符号を隠さない。
- [ ] 有界二重複体又は具体的filtrationの次元比較を、後続が使う範囲で証明する。後の頁で次元が減ることを許し、退化は仮定しない。
- [ ] Run15/16で実体化するsource・cut・tower・connecting rankの入力を列挙する。このrunだけでordinaryや端点のactual移行全体を完成とは報告しない。

## Task 6：同標数の体拡大 I_FIELD

**Consume:** 体拡大L/k、P加群M、Task 2–4の自然な複体と有限性。

**Produce:** scalar extensionとKoszul/Tor homologyの自然同型、graded/total Betti不変性、actual Gと関連商/核への適用。

- [ ] 変数集合を保持したL⊗ₖP≃L[Xσ]と、複体・homologyのflat base changeを証明する。
- [ ] 次元保存からBetti不変性を得る。有限体→無限純超越拡大→元の体という後続cutの使い方に接続できる形にする。
- [ ] 無限形式級数環全体のtensor同型に依存せず、Run12のactual graded比較と各piece/加群の自然性を利用する。
- [ ] 標数2の体拡大と非斉次元を含む自然性を検査する。異なる標数間のBetti/rank一致は主張しない。

## Task 7：後続に必要な標準単項式・rank比較の基礎export

- [ ] `StandardMonomials.lean`等で、実際のleading term・除法・normal form・商の基底への橋を必要範囲で供給する。汎用Buchbergerの全実装は必須ではない。
- [ ] O_HARMONIC用の初項rank比較・block三角化・対角±1 minorに必要な一般補題を確認し、足りないものを証明する。
- [ ] 定数±1のminorが任意標数で非零となることを証明する。有理重みは整数rankの数値評価であり、係数体の中で分母を割る操作に置き換えない。
- [ ] 特定sourceのinitial idealの等式・全競合のチェック・harmonic不等式本体は後続で実証明する担当を残す。生成元の初項を並べただけでGröbner基底や商の独立性を済ませない。

## Task 8：通しの受入検査・台帳・公開

- [ ] `tests/Koszul*.lean`、`tests/BettiBaseChange.lean`等で、全actual変数・通常Tor比較・有限性・自然性を通した例を作る。
- [ ] ℕの接錐、二生成元の特異例、jumpのあるactual GとT/A/N/Q・同jump商を検査する。1変数P=k[X]のP/(X²)ではBetti (1,1)、n変数Pの残余体kではβᵢ=binomial(n,i)、自由加群Pではβ₀=1・正次数0を検証する。
- [ ] chain groupの有限性を誤って仮定していないこと、source/target/S₀/cutの変数数、標数2、H₀とtop、同じ写像の自然性を重点確認する。
- [ ] 新規ソース・全新規宣言とinstanceの公理依存・既存Block01–12の必要な回帰・過去監査境界・固定依存hashを検証する。適切な検証後は、根拠のない反復検査を増やさない。
- [ ] `verification/block13/`、監査ZIP、宣言/仮定/所属ファイル一覧、`LEAN_PROGRESS.md`、原稿変更台帳を確定する。通常commit/Push後、リモートSHAとclean worktreeを確認する。

## 終了と次runへの引継ぎ

**型だけの枠組み、任意のsquare-zero map、有限次元性を仮定したBetti定義、未証明Tor比較を引数に持つ定理だけではRun13完成としない。**
Task 1–7の必要なexportを実証明で供給し、Task 8でactual例まで通す。
X_BASICは複数の理論を束ねた頂点なので、完了したexportと未完を宣言単位で列挙し、未完があれば全体閉鎖を主張しない。
大きな数学的障害や実際の実行制約が出た場合は、閉じた定理・未完の正確な宣言・理由・次の必要入力を保存する。

Run13後には実測を基に20 run計画を再校正し、Run14へ渡す体拡大・Tor・有限性のactual exportを示す。
この指令は貼り付け/参照用として準備したもので、監査スレから実行スレへの直接送信は行っていない。
