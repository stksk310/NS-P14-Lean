# Run17 監査引継ぎ

基準work: `584f92d8c1a7fc1e2413f606b661fc9b81f472cd`。
指令commit: `845b9c2ff3a047e62d53f639901452a030ca7981`。
Run16外部監査: `5ced6cc564e5c69bebcd7a852463091e2e276661` (11 ID PASS、修正要求なし)。
最新版のgateは`RUN17_CLOSURE_STATUS.json`を参照。

## 必須命題と証明本体

`audit/run17/RequestedGoals.lean`は二つの元の命題をPropとして凍結。
SHA256: `54dc3a2a4f0f204388751deaaffb7d77d673ac80444b646d1794a2b984891888`。
`ClosedGoals.lean`は全く同じPropを証明し、追加前提を置かない。

Kneserは`KneserCore.lean`の`Finset.add_kneser`と`Kneser.lean`の`kneser`。
Bakšys–Dillies / MiscYDの実ソースを固定mathlib上でbuild。
原ソースhash、metadataだけの変換の逆照合、Apache licenseを保存する。
`KneserRuzsa.lean`の未完成証明は取り込んでいない。

SCは`SharpSequence`→`SharpRearrangement`→`ConnectedSequence`→
`ConnectedRepresentatives`→`SavchevChen`。
Levのconnected方針を位置集合の導出木で実証明する。
sharpの逆向き包含、一意性、同値項の反復、極値subset、
全sharp終端の一意性、正係数区間、addOrderOfの整除、実unitの逆という主鎖。
一般列を二値列へ縮めず、重複は`Fin`位置とmultiset/List同値で保持する。

## consumerの監査点

- nAは独立和、0A={0}。実stabilizerはSet/Finset actionの同一性を証明。
- 任意Hのcoset計数とstabilizer preimage、最終和の非周期商、部分和stabilizer包含。
- ceil半分の増分、個別nonunitを許す三点、実H=位数2の四点例外、antipodal表示と非例外成長。
- 同じDの正規化a_i、法u。core degree/residue↔nA↔実shortestDegree。
- Wの定数1と0層を保持。有限layer cake、同じAでの成長和、q=2の二次上界。
- 実QCの生存から任意の非空位置選択を扱う零和自由性を証明。
  零和選択は実端点因子となり1≤K<選択長。
- SC unitは列の補助操作。元source・R/Hxへのunit変換/反射不変性を仮定しない。
- 二値consumerはunit・代表和・ラベルと個数の同時交換・元群でのmodular relationを返す。

## 再現

`PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_run17.py --fresh-test-cache`

実行環境外では同じ固定toolchainをPATHへ置く。
全Run01–16 tracked baselineをbytes固定 (root import追加と共通進捗文書追記は元の全prefixを保持)。
test cacheと新規productionのlib/irを退避してからrootを再build。
全fixtureをimport依存順に、相対olean出力先で実行する。
全新規・生成宣言とrootに対し通常/explicit型・source hash・公理を抽出。
Run15元8目標、Run16全11 IDのClosedGoalsも再実行。
verifier/packager/数値入力/原典provenanceをsource hashへ束縛する。
旧数値checkerのhard-coded出力先は、原コードと入力をtemporary rootへコピーして隔離。
旧座標JSONの実測secondsを含む原本bytesを保持し、新しい結果はRun17側へ保存する。

独立有限回帰: u≤8の非空集合対86,368、反復4,554、長零和自由multiset 92。
u6/u9の指定SC例、半分境界の反例、実W=10、標数2の実QC生存語も受入に含む。
有限回帰は一般形式証明の入力ではない。

監査ZIPは最終gate通過後、全entry集合・全SHA・CRCを再照合して生成する。
ZIP自身のSHAは隣の`.zip.sha256`を正本とする。

`attempt_01_legacy_write`は旧checkerのseconds書き直しを最後のbyte照合で検出した試行、
`attempt_02_full_fixture_elaboration`は追加full-group受入の型展開を修正するため中断した試行。
旧履歴として保持し、完成判定には`final/verification.json`だけを使う。
