# Run16 監査引継ぎ

基準commit: `447b7ae782414b739968a2a3009dd3a52ae230d0`（Run15完了）。指令commit: `0cda4e8597ea1bafa8770b851ff2373973ee0e03`。実装の正本はworkと `NSP14/Endpoint/`、統合出口は `RowPackage.lean`。

## 再現

固定toolchain/mathlibを保持したcheckoutで `python3 scripts/verify_run16.py --fresh-test-cache` を実行する。Lean/lakeはPATHに必要。出力先は現在のcheckoutから相対的に構成し、旧worktreeの絶対パスを再生しない。project test cacheは別の一時ディレクトリへ保存して空から依存順にコンパイルする。

`verification/run16/final/verification.json` がコマンド一覧・実測、`declarations.json.gz` が全新規宣言（instance・constructor・recursor・自動生成helperを含む）の通常型/explicit型と公理依存、`SOURCE_SHA256.json` が源泉、`MANIFEST_SHA256.json` が検証証跡を束縛する。許容公理はpropext、Classical.choice、Quot.soundだけ。自己依存と許容外をscriptが拒否する。Run15以前の原本をbaselineのbytesと照合して保持する。

## 重点

- 広いEHでdu<m、gcd(m,u)=1、CMを追加していない。狭幅では元のcarrier・元の完備接錐へ戻る。
- Eの2変数、Tのq変数、全表示のq+2変数、実際の作用と変数順序を区別する。
- kernelはすべての長い表示を含むN=M∩T。停止周期はu/gcd(m,u)。T単独をactual kernelと呼ばない。
- PGとPCは異なる。実kernel完全列の補償と第0行、top行を維持する。
- Gのk有限性を使わない。homologyとsocleの有限性を個別に証明する。
- Rは実socleの基底と核の角による正確な点数、σ_CはQC内部socleの別基底。Rhatは同じ向きから構成。
- 一般Artin商の評価は実斉次idealと実Gröbner正規形に接続。符号付き差はℚ上。±1 minorは標数2でも有効。
- 単項式T商の主張はq=2だけ。q=3の生存二次関係と反射でHxが異なる試験を保持。
- 三具体例のPC/PG/Rは任意体でLean等式。有限座標799例は独立した回帰であり、一般証明の代用ではない。

原稿上の証明経路の変更と11 ID対応は `RUN16_PAPER_CORRESPONDENCE_JA.md`、後続担当と実測による再校正は `RUN16_PLAN_RECALIBRATION_JA.md`、実施時の判断はexecution ledgerに記録する。
