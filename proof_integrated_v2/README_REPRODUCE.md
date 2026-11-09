# V02の読み方と再実行

主成果は [日本語の単一証明本文](NS_P14_INTEGRATED_PROOF_JA.md)。
[置換台帳](PROOF_REPLACEMENT_LEDGER.md)、[依存表](PROOF_DEPENDENCY_MAP.md)、
[全域coverage](GLOBAL_COVERAGE_MATRIX.md)、[統合監査](INTEGRATION_AUDIT_JA.md)、
[実行記録](verification.json) を併せて保存する。

## 必須計算の再実行

このディレクトリで、Python 3.10以上を用いて次を実行する。
すべてPython標準ライブラリだけで動き、外部データ・旧証書・他checkerを読み込まない。
数学的な有限化と無限範囲の処理は本文にある。

~~~sh
python3 -B checks/n4/check_shorter_n4.py > audits/n4_run.json
python3 -B checks/n4/referee_core_audit.py > audits/independent_n4_run.json
python3 -B checks/verify_scalar.py > certificates/scalar_arithmetic.json
python3 -B checks/verify_width.py > certificates/width_arithmetic.json
python3 -B checks/verify_small_ordinary.py > audits/small_ordinary_run.json
~~~

| コマンド | 期待される結果 | 証明中での意味 |
|---|---|---|
|check_shorter_n4.py|196対、負の粗上界は(3,1,2),(4,1,3)だけ|本文N21–N22の全offset評価。m,dの列挙0|
|referee_core_audit.py|196対版と493対追加監査版で同じ二例外|二つの独立core計算法の照合。493対は必須範囲ではない|
|verify_scalar.py|全係数恒等式、6小rank比較、rank10 margin=181/8400、351補助診断|本文S1–S31。無限域の根拠は正項分解・正二次式|
|verify_width.py|疎幅4表、一般e≥10式、保持した高次式、小幅容量表が全係数一致|本文W4、W18–W22。parameterサンプルではない|
|verify_small_ordinary.py|83profile・665行比較、不足0、最小余裕67、5tail anchor|本文O1–O18の有限化後の整数補題|

assertを用いるscalar・独立N4 checkerは <code>-O</code> を付けると明示的に拒否する。
通常の実行コマンドを使うこと。

## 保存した必要データ

- <code>certificates/n4/SHORTER_N4_CERTIFICATE.json</code>：全196対のPC、socle、
  Hx、W、R上界、第一行余裕、および三つの高次行多項式。
- <code>certificates/small_ordinary.json</code>：83profileのHilbert列、最大変数別生成元数、
  source上界・target容量、5本のtail anchor。
- <code>certificates/scalar_arithmetic.json</code>、
  <code>certificates/width_arithmetic.json</code>：厳密恒等式と有限有理数の再計算結果。

小ordinary profileの意味内容SHA-256は
<code>e10afc786ae3d55a1d35e65533696792ebf4ff4daea18c61806594623d09c65a</code>。
これはJSONの83profileを正規化したもののハッシュであり、JSONファイル全体のハッシュとは異なる。
全配布ファイルのSHA-256は <code>MANIFEST_SHA256.json</code> にある。

## 追加監査と元資料

<code>audits/FINAL_MATHEMATICAL_REVIEW.md</code> は新稿全文と旧稿の必要部分の独立点検、
<code>audits/COVERAGE_REVIEW.md</code> は全域・全行・参照・局所記号の独立点検である。
いずれも公刊査読・Lean kernel検証という資格ではない。

<code>audits/commander_historical_comparison.json</code> は添付Commander比較コードを、
保存された旧13921行証書と新196行証書へ適用した追加監査結果。
旧証書はこの軽量パッケージの数学的依存ではないため同梱しない。
同コードは入力物のパスだけを作業環境に合わせ、計算法を変えず実行した。
入力ZIP・各入力文書・旧稿の同一性は <code>SOURCE_RECEIPT.json</code> で追跡できる。

旧統合証明ZIPと旧証書は元の作業領域に保存されている。
新ZIPは本文・必要コード・必要な小証書・統合監査を含み、探索ログや旧大型campaignを含まない。

## 判定の範囲

<code>INTEGRATED_PROOF_CANDIDATE_PASS</code> は、明記した公刊入力と厳密有限計算を用いる
統合証明候補の編集・接続・検算が通過したという判定である。
内部の旧境界を未証明仮定として再導入していない。
公刊定理自身の再証明、学術誌の査読、Lean形式化の完了を意味しない。
