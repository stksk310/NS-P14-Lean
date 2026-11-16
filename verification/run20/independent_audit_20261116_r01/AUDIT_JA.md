# Run20 / 全P14 最終独立監査（2026-11-16）

対象HEAD: `a5e122a4d09536b1609c5faa8d419f8faf81671f`。既存Run19監査修正 `342fbdd` を含む最新workを明示fetchし、隔離worktreeの `audit/run20-20261116` で監査した。既存の最終レビューのPASSは採用せず、新しい数学的読解、依存対応監査、型codec監査、独立cold再検証、Git/ZIP照合を実施した。

## 判定

**PASS。新規Critical / Important / Minorはすべて0、修正不要。I_PARTITION / I_MAINおよび必要入力は閉鎖済みで、V06の全P14主定理までLean化完了と判定する。**

独立cold再検証335項目・311 fixture・15,774宣言はすべてPASS。数学的追加公理はなく、許容依存は `Classical.choice / Quot.sound / propext` のみ。検証終了コード0、独立crosscheckも終了コード0。

## 無条件の公開主定理

公開入口は `NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion`、最小importは `NSP14.Main`。引数は元の `S : NumericalSemigroup`、元の `k : Type`、`[Field k]`、すべての `i : ℕ` だけである。結論は次の実対象の比較:

```lean
totalBetti k S.AtomExponent
  (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
totalBetti k S.intervalCompletionAll.AtomExponent
  (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
    (S.intervalCompletionAll.FormalTangentAlgebra k)) i
```

右辺のcarrierはliteral `AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom)`。双方とも自身の実最小原子変数を使う。e≥2、正幅、CM、gcd(m,u)=1、Infinite/CharZero、別体、行上限、比較証明書を追加前提にしていない。`I_MAIN` / `I_PARTITION` の元の凍結受入と、参照される分割predicateの本文も保持されている。

## 数学・全域分割・実consumer

`parameter_partition` は e=1 / e=2 / e=3 / e≥4 ordinary / e=4 narrow / e≥5 narrow の6領域の一意性を証明する。w=m−1はordinary、w=m−2はnarrowへ入る。e=1の幅0・literal [1,1]、conductor witnessが異なる同carrierのtransport、actual cutのr=2例外・δ=0/空塔、physical幅V=d*u=wを確認した。

各branchは元S・元kのproduction出口を直接用い、同carrierのactual Betti transportで同じtargetへ接続する。ordinaryの体拡大は実baseChange同型から元のkへ下降する。e=3は必要比較をone-letter endpointから直接証明する十分な別証明。N4は新cubicと幅4の全m/全j実kernelを使い、e≥5 narrowもphysical targetに支払う。Mainやbranchの結論を仮定に戻す循環はない。

全iを保持し、source topとtarget topを区別する。実fixture `<6,7,9,11>` はsource第5行=0に対しliteral target第5行=5であり、source消滅からtarget消滅を誤って推論していない。任意体版とQ/F2/F3の最小公開API fixtureもある。

詳細と読解範囲は `MAIN_MATH_REVIEW.md` に保存した。これは全低水準補題を一から再証明したという主張ではなく、cold kernel再検証と合わせる独立した意味・経路監査である。

## 必要入力・V06・50 ID

`DEPENDENCY_PAPER_REVIEW.md` のとおり、旧registryの50 IDの原文/量化は全件一致。Green特殊版、BHP/EK、Kneser、AP Betti/接錐、LTV必要比較、Savchev–Chenを実proof出口とactual consumerまで追った。引用名のaxiomや未証明certificateで閉じていない。

全j競合の実kernel、元R/Hx、PC−PG補償、任意標数と元の体、N4新cubic、全branchの主依存を保持する。Mainの静的import閉包670 moduleにStopping、旧固定profile/certificateは入らない。一般Green全次数、LTVの追加3線形評価、一般initial-ideal等式など、V06主定理に不要な強化を必要な形式化済み入力として数えていない。完成主張はV06の無条件主定理とその必要入力についてのものである。

## 全環境型・公理・codec

`TYPE_CODEC_REVIEW.md` と今回実際に実行した独立 `type_codec_probe.py` / raw stdoutを保存する。全1,019 module、15,774宣言（private 3,679、instance定義・生成helperを含む）を直接 `import all`、別inventory、固定名集合、28 canonical helperと照合する。33 moduleは実際にimport-onlyである。

全宣言のnormal型・元kernel型・binder名のみ正規化したexplicit型・universe parameter・実collectAxiomsを保存する。独立probeでは元/正規化DAGの全nodeのshape・Name/Level・binder・child<parent参照を検査し、全15,774型の独立構造hash一致を確認した。旧15,542宣言の全名を保持し、旧公開11,928宣言のnormal/explicit型・universe parametersも一致する。

codecの実行中roundtripは元MData配列を保持して構造復元する。保存metadataは診断snapshotであり、汎用self-contained外部JSON decoderとは扱わない。今回のsnapshotはboolean marker 3種で、数学的型の引数・universe・binderの省略に使っていない。型probeは保存物の独立検査であり、fresh Lean実行を代替しない。

## 独立cold再検証

固定HEAD a5e122aで次を実行。完了までHEAD/source/既存証拠は変更しなかった。

```sh
PATH=/workspace/audit-tools/lean-4.36.0-rc2-linux/bin:$PATH python3 scripts/verify_run20.py --fresh-project-cache --baseline-cache /tmp/run20-independent-base-donor-hi_lzrtc/.lake/build --output-dir verification/run20/runs/independent_audit_20261116_r01
```

現projectのlib/IR/tests/auditsを退避してcold再構築、固定mathlib等のpackage cacheは保持した。旧baseの比較専用donorはBASE 07fe1edのsource 1,006件をGit実バイトに照合してからcacheをコピーし、検証器がさらに独立した隔離先でsourceを検査・build・全環境型監査を再実行する。donorや元worktreeを書き換えない。

335項目・311 fixture・全1,019 module / 15,774宣言がPASS。旧15,542宣言・公開11,928型とuniverse parametersを照合し、61件の負例テストと13件の実Lean codec controlsもPASS。生8partの全宣言と最終一覧、command map、source/Git bytes、evidence manifest、既存証拠10,731件のbytes/filesetを独立crosscheckで再確認した。今回生成した全型記録は公開R03とGZIP bytesまで完全一致し、既存保存物の独立DAG検査結果とも直接対応する。

summary SHA256: `29243c606c91138d53214e8893cea4bd65a40b25ba6d8877c2134353f9e1b54d`

evidence manifest SHA256: `1eacb2e906496de1f0086d91f44ad33f3f406c6d7131468225a9d908c7717c8a`

全実行証拠: `verification/run20/runs/independent_audit_20261116_r01/`。hash・集計・scopeは `fresh_crosscheck.json` と `audit.json` に保存した。

## 配布済みR03の独立binding検査

`published_bindings.json` と `published_binding_check.py` の実行結果を保存した。source 1,674件はcurrent/proof `1a5c6bac9a4fd38a8bc5d13b4c7372e654466e6e` / reviewed evidence `041adc1024109644378b2be5aed95276da6b65f2` で一致。evidence 488件の完全fileset/hash/Git bytes、全335コマンド/311 fixture、8partの生宣言streamと保存全15,774宣言、review本文・decisionを照合した。proof→evidence→review `dd77e23`→package `f5f8908`→完了receiptの履歴も整合する。

ZIP: `artifacts/NS_P14_LEAN_RUN20_COMPLETE_20261116_R03.zip`

SHA256: `7145c7302a7267041897a6f0993d8b2c82b9755b44412efd6f4dfe064c473d94`

全2,168 entryは重複・危険pathなし、CRCと全payload hashが一致し、review本文・凍結source/evidence manifest・再現手順を実際に含む。package commitのZIP Git bytesも一致する。これは固定Git履歴と依存取得を使うproof/evidence bundleで、toolchain/mathlibまで含む完全offline checkoutとは表示していない。

## 証拠の保存と公開

既存R03の証明・review・完了receipt・ZIP、過去の失敗/中断試行は不変。source-bound status文書と検証summaryの公開前フラグは凍結段階を記録しており、別の `RUN20_COMPLETE_20261116_R03.json` が公開完了を記録する。今回の独立監査はさらに新しい記録として追加する。

検証中のsource manifestは公開R03と1,674件すべて一致。監査では修正を要する指摘は0。数学・全tests/auditのLean・検証器・原稿・依存pinを変更していない。追加は今回の独立再検証証拠と監査記録のみ。Push観測は監査commit後の別receiptへ記録する。既存の完全束を再認証した別ZIPは作らない。

この監査フォルダのPython probeは実行時の固定workspace pathを保持する歴史的記録である。Main/依存/codecの読解報告はそれぞれ実施範囲を明記し、保存物だけの検査をfresh Lean実行と混同しない。今回の最終判定はそれらと独立cold実行、実Git/ZIP照合を合わせた結果である。
