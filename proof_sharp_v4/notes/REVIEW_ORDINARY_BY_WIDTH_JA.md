# Ordinary章の独立読解レビュー

対象：`chapters/02_ORDINARY_JA.md` の O1–O12。
照合先：読解対象SHA `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` の V02§2–11、
`auditability_search/ORDINARY_PAPER_REDUCTION_JA.md`、`ORDINARY_REDUCTION_REFEREE.md`、
`NSP14/Ordinary/LargeSeed.lean`、`LargeScalar.lean` および同章が明示する資源・Tor構成。
この担当は幅章の作成担当であり、ordinary章の作成には参加せず、ordinary章を編集していない。

**判定：今回確認したordinary経路に要修正の数学的所見なし。**
これは本稿全章や公開定理の再証明、あるいはfresh Lean buildの認定ではない。

| 監査項目 | 確認した内容 |
|---|---|
| actual座標 | headの非Apéry部分Nがactual S0-イデアルであり、Qが実Apéry基底を持つ。T↔Nは全体同型とせず、逆向きfiltrationの同jump層のみを同定する |
| jump上限 | IQの生成次数≤ν+1、terminal次数≥1、head作用のjump非増加から全headへ上限を伝播する。次数差sを保持する |
| 最短offset | prefixの最小性、cycle除去、atom剰余での非増加を用い、同じLρから有限総量とterminal jump総和を得る |
| cutと塔 | Green切断を一度固定。Us/Xs/Ms/Ksは同じactual Aから構成し、各評価で別のcutや別の資源列を選び直さない |
| 資源列 | Apéryとheadの寄与区間、同剰余の区間非交差からHt≤m−1。H0、H1、ΣHtの全制約は同じ列で同時に成立する |
| 調和rank | 同じ体上のGroebner block三角rank比較、単項式商の±1 minor、有理数としての指数重み平均を区別する。標数間のrank比較や体内除法は使わない |
| Tor三段 | 0→X2→A→B、同jump strata、0→Ks→Ms→Xs+1の各完全列から非負connecting rankだけを落とす。x-Koszul後のd2退化を仮定しない |
| H0補正 | G/(x,E)G=k[Z]/(Z)^2を正確に扱うことで(O13)の定数qを差し引く。正のhomologyのKoszul鎖上界と0行を混同しない |
| top | cr=0の有限長P-加群側のEuler式とj=rの重みを保持。full Betti移行でj>rのtarget係数は非負に余る。e−iによる除法はない |
| r2・δ0 | r2にはtriangular lower boundやSidon角除外を課さない。δ0ではν1、N=T=0、塔空としてH0=0と全式が整合する |
| r3 | H1≤M−6とH1≤3δを同じ列で適用し、first/second/topの必要係数をそれぞれ満たす |
| small scalar | fixed cutoffは資源の台を切らない。負のtail係数だけを非負資源から落とす。(O17)の正値性ではs,tが非負整数であることを明示する |
| Sidon角 | actual maximal Q2に限って差写像を構成。cutからの含意はr≥3に制限し、r2の反例を取り込まない。必要なr6/7/8の角だけを除く |
| large rank | r≥9、e≥10、δ≥arが明示され、調和障壁はr10以降の帰納法とr9の一seed。床比較OL8で両偶奇を扱い、有理シフト0<t<1もOL9の形で扱う |
| target | actual ordinary interval completionが⟨m,…,2m−1⟩と同じ半群であることを使い、各環自身の最小多項式表示で比較する |

## 独立算術検証

SymPy 1.14.0で章の式を独立に入力し、次を確認した。

- (O16)の有限和整理、Gのe係数A、および任意の基点E0についての(O17)の差を記号的に0と確認。
- r4–8の五行表のg,A,bを有限調和和から厳密に再計算し、表示された分子・分母15個すべてに一致。
- r3第一rankの差の非負係数表示に一致。
- (OL4)の調和障壁増分quartic、(OL5)のthreshold同定、(OL6)のthreshold下界差を記号的に確認。
- (OL7)のseed–slope/correctionとforward-stepの二恒等式、(OL8)の連続床比較を記号的に確認。
- `B(10)−H28=1833472237/80313433200`、`G9(10,45)=5845533/7436429` を厳密有理数で再計算して一致。

全検査は成功した。任意次数・任意rankの全称性を数値範囲の検算で代替していない。
本レビュー担当はLean/lakeや既存回帰スクリプトを実行していないため、fresh build成功とは記載しない。
