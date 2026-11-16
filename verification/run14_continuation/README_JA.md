# Run14継続の再現・監査

基準途中版8040c90。判定・件数・実測時間はverification.json。
固定Lean v4.36.0-rc2 / mathlib 139105d、依存変更なし。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_run14_continuation.py --fresh-test-cache
python3 scripts/package_run14_continuation_audit.py
```

通常のelan環境ではPATHの指定は不要。
全旧production/test/dependency、旧verification/run14、旧PARTIAL ZIPは基準commitとのbyte一致を確認する。
後から取り込んだaa6bf4cのRun13再現性修正・証拠も、そのcommitとのbyte一致を確認する。
最初にNSP14と、テストが直接使うZMod field/RatFuncの依存targetを明示してbuildする。
root importは旧rootの完全なprefixを保持する。
全旧検証43コマンド、新受入3本、旧命題の型とその5本の証明、build、公理監査を実行する。
警告・追加公理・自己axiom依存・新規宣言coverageの欠落を拒否する。

- `declarations.json.gz`：環境から列挙した全coreおよび新受入/監査宣言、公理、所属module。
  全新規宣言（structure projection・constructor・recursor・補助定義・instance含む）は明示型も保存。
- `environment_axioms.log.gz`：監査の全出力原本。
- `SOURCE_SHA256.json`：新規source/test/auditと固定依存・status・検証scriptのhash。
- `FINAL_REVIEW_JA.md`：単一fresh reviewerの結果とroot所有の未評価項目。
- `REVIEW_PACKAGE_JA.md`：レビュー開始時点のpackage（検証の途中状態を記述する歴史的記録）。
- `fresh_test_cache.json`：最終実行は空のproject test cacheから開始。旧cacheは/tmpへ退避。
- `FIXTURE_CACHE_RED.log`：旧順序の実consumerがRun13Fixtures.olean欠落で失敗するRED。
  最終suiteはactual public import依存の順序でfixtureを先にcompileする。
- `AUDIT_COVERAGE_RED.log`：匿名example二本が環境coverageに残らないことを検出した失敗原本。
- `green_la_red.log`、`volume_red.log`：実装前の欠落exportを検出したRED原本。

Leanのpublic moduleがproofを輸出時にstub化するため、exported_kindがaxiomであっても
それ自体を追加数学公理とは判定しない。collectAxiomsによる実依存が許容3公理内であり、
宣言自身を公理として参照していないことを検査する。元のkindも保存し、情報を隠さない。

gzipはJSONやログを省略せず圧縮するためのもの。必要なら標準gzipで展開する。
過去の型一覧・検証原本は旧ディレクトリにそのまま残す。

Run14の完成範囲はGreen/cut/offset/tower/resources/Sidon/既存数値全行比較まで。
actual Tor評価・target Betti同定・最終P14はRun15以降であり、このPASSからは推論しない。

最終実測：50/50コマンド、168.52秒（各検証時間の合計）、3217環境宣言、全新規544宣言。
内訳はcore514、受入/監査30。旧凍結241件と、取り込んだRun13修正74件を照合。
project test cacheは空から開始し、Run13Fixturesをconsumerより先に生成した。
