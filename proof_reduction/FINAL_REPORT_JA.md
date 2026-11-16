# NS P14 証明簡約の結果

2026年11月9日。判定は **NEW_HUMAN_REDUCTION_PROVED**。これは今回の簡約についての判定であり、P14全域の無条件完全認証ではない。

**前稿のB・Wという大きな継承ブロックを解きほぐし、最後に独立認証を残す範囲を「物理幅が狭い4生成元N4」に絞った。** ordinary側は10生成元以上の単一scalar、2・3本cut、83組の小整数評価と5本のtailで処理する。幅側は5生成元以上を有限coreなしで処理する。

読む本体は [HUMAN_PROOF_REDUCED.md](HUMAN_PROOF_REDUCED.md)。幅側と小ordinaryの詳細証明は、それぞれ [WIDTH_REDUCTION_PROOF.md](WIDTH_REDUCTION_PROOF.md)、[SMALL_ORDINARY_PROOF.md](SMALL_ORDINARY_PROOF.md) に分けた。

## 実際に減った依存

| 対象 | 前稿 | 今回 |
|---|---|---|
| ordinaryの大きいe | e≥13 | **e≥10**、actual rへ直接適用 |
| scalar算術 | 200無限ray＋H210の別tail | **H23の評価1個＋小有理式7個＋正係数多項式恒等式**。r・δ・eの紙上帰納で全域を処理 |
| 最大rank包絡 | r0=p(δ)、単調性、過大cutと数値包絡の区別 | **不要**。δ≥binom(r+1,2)のactual rを直接使う |
| harmonic補題H | 初期加群、Peeva、EK、lex、coupling | **初項基底のGaussian消去、三角小行列、Koszul単位小行列と計数** |
| volume | Elias microinvariant上界 | **最短offset経路で非atom剰余を数える初等証明** |
| 小cut | e≥13のV下界 | r2は二つの評価をV=3で使い分け、r3はH1≤M−6を保持。**ordinary e3/e4も直接処理** |
| 幅側W | e≥8 | **e≥5**。5・6・7生成元の68・785・210 core campaignが不要 |
| 幅tail | W1全体、平方根閾値、anchor帰納 | u≥2e−2のrestricted tailと正係数式だけ |
| 11・12生成元 | 1,961＋2,562 first-hit profilesと実構造補正 | **主証明から全て不要**。新しいe≥10 ordinaryとe≥5幅側に吸収 |
| ordinaryに残る小e | 巨大な全Hilbert遷移graph | 最大first-hitの一列へ還元。**83組・665整数比較＋5本の紙上tail** |
| 最後の継承境界 | e≤12のB全体 | **true narrowのe4だけ：N4** |

比較件数は、最終組立てで必要な領域を他の補題で吸収した後の件数である。有限標本の成功から全sourceを推定して減らしたものではない。

## 証明を簡単にした二つの核心

Hでは、次数tの標準単項式mとj集合Fに対し、固定した変数vを避けるrowにsource列 \((m/x_v,F\cup\{v\})\) を対応させる。部分行列は対角±1になる。そのrank下界を有理重みで足すだけでharmonic係数が現れる。一般加群もラベル順の三角小行列で同じ下界へ還元できる。有限標数を除外する操作はない。

volumeでは、least-offset経路の最初はatom剰余でL=1。次の頂点がatom剰余ならLは増えず、非atom剰余なら高々1増える。非atom剰余はδ個しかない。これでL≤δ+1と必要な総和上界が同時に出る。

## 反証志向の点検結果

Nのideal性、terminal–headの基底対応、反対向きのjump filtration、H1の厳密計数、同一cutでのTor移行、top rank、actual targetを点検した。Hには別の直接証明を構築した。新scalarの偶奇差分、cutoffの切替え、正のe傾き、多項式の全係数は独立の別導出でも一致した。

今回読解・再構成した範囲で、主鎖を壊す反例や実際の欠落は確認していない。既知の補助waterfill一般文の符号問題は、本証明が使用しないので再導入しない。

## 残る作業

N4の原文とコードは存在する。一部再現も成功した。しかし、primitive／nonprimitive true narrow、例外族、全パラメータの還元を含む祖先全体の独立認証はまだ終わっていない。したがって最終主張は **N4と明記した公刊入力を採用した条件付き全域証明**である。[依存台帳](DEPENDENCY_AND_GAP_LEDGER.md) に範囲を固定した。

Lean化はまだ開始していない。JSONや未証明axiomをP14の証明として扱わない。今回の成果は、形式化すべき補題と残す境界を実際に減らした数学的簡約である。

## 再現

`proof_reduction` を作業ディレクトリとして実行する。

```sh
python -B checks/verify_scalar.py
python -B checks/verify_small_ordinary.py
python -B checks/check_width.py
python -B checks/check_harmonic.py
```

scalarの任意診断は `--diagnostic 210` などで追加できる。この診断はr=p(δ)の数値列だけであり、全actual rの普遍保証は本文の帰納法による。有限計算のfresh実行と証明の範囲は [verification.json](verification.json) に記す。
