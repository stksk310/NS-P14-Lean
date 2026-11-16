# Run20 全環境型・公理／DAG codec 独立読解監査

対象: `/workspace/NS-P14-Lean-run18`, branch `audit/run20-20261116`, HEAD `a5e122a4d09536b1609c5faa8d419f8faf81671f`。主保存証拠は coordinator の訂正に従い `verification/run20/runs/release_20261116_r03`。R02 は `Part00/01` の途中streamのみで完成認証記録ではない。

**結論: 下記scopeで PASS。Critical / Important / Minor として報告すべき実装欠陥は見つからなかった。** ただし保存metadataは汎用的に復号可能な独立codecではなく、全kernel再検査をこの監査人が実行したという結論でもない。

## 方法・実行制限

既存reviewの結論を採用せず、`scripts/verify_run20.py`, その `verify_run19.py` / `verify_v06_alignment.py` の継承先、`verification/run20/sources/audit_parts.py`, `kernel_type_codec.inc`, `check_kernel_type_encoding.py`, `scripts/check_run20_guards.py` の該当箇所を読解した。保存R03の全declarationを独自Pythonで集計・構造照合した。Lean / Lake / build / 検証script本体 / checker / packager は実行していない。repo/source/evidence/cacheは変更していない。coordinatorの並行作業による新規untracked出力はこの監査の書き込みではない。

今回実際に実行し、exit 0を確認した再現可能なpure-Python probe（repoコードをimportしない）:

* program: `/tmp/run20-type-codec-independent-probe.py`
* program SHA256: `8201a776d7ed256e489d371daa230522ae284088ec84119508ace404fe3e3d17`
* command: `python3 -u /tmp/run20-type-codec-independent-probe.py > /tmp/run20-type-codec-independent-probe.stdout`
* raw stdout: `/tmp/run20-type-codec-independent-probe.stdout`
* stdout SHA256: `58c4c4b5ac9c493e28943ae6b91b136c47c69749b2771f7812b2d74972d531ec`

このprobeは保存済みDAGの整合性・相互一致を独立に確認する。実際のkernel `ci.type` が保存物と同一であることのfresh実行証明ではない。追加参考として upstream Lean `v4.36.0-rc2` の `Expr.lean` と `CollectAxioms.lean` もread-onlyで読んだ（ローカルインストールソースはアクセス不可）。その参考読解をローカルtoolchainのfresh検証と扱っていない。

## PASS: 全module・全宣言・private/helper/instance定義の範囲

* `verify_run20.py:85-87,99-105,123-134` はroot `NSP14.lean`、`NSP14/`、`tests/`、`audit/` 以下の全Lean moduleを列挙し、元module名で判定する。`verify_run19.py:110-117` が全moduleを直接 `import all` に変換する。namespaceやpublic/theorem/instanceという種別による除外はない。private名・生成helper・instance定義もenv.constantsにあれば同じ型／axiom経路へ入る。
* `audit_parts.py:15-31,39,45-78` はmodule選択の重複・欠落、各partの全import metadata、row名の重複、別途のenv inventoryとの一致を検査する。保存8partすべてについて直接`import all`の集合が独立のfilesystem module集合と一致し、選択集合は相互非重複で全件を覆い、codec本文も現HEADの `.inc` と完全一致した。
* 全1,019 module = production/root 708、tests 261、audit 50。全15,774 unique row = production/root 13,078、tests 2,523、audit 173。うちprivate 3,679。宣言を持つmoduleは986、33 moduleはimport-onlyであり、後者を「rowなし＝欠落」と誤認しない。import metadataには全1,019 moduleが存在する。
* 別名取得source `DeclarationNames.lean` / `DeclarationNamesHash.lean` はともに全1,019 moduleを直接 `import all`。両保存logの `complete_name_inventory`、両expected JSON、R03 metadata inventory、実際のrow名集合が全15,774名で一致した。row生成ループと別のenv走査である一方、独立のLean実装やsource parserではなく、同じkernel環境のmodule所有情報を使うinventoryである。
* `verify_run20.py:146-157,288-289` はrow/inventory/固定expected集合と全base名存続を照合する。`verify_run19.py:18-27,105-108` の固定28 helperについても、独自AST literal読解から求めたmodule/name対がすべて存在した。guardは単独private rowの脱落、rowとinventory両方からの脱落、同一module内のnamed helper脱落、part欠落／重複を検査する (`check_run20_guards.py:97-128`)。

この監査のinstance coverageはinstanceの**宣言定義とその型・依存公理**である。instance属性・priority・登録extensionを別表へexportして照合する機能ではない。現在の型・公理監査のscopeにはこれを超える保証を含めない。

## PASS: Exprの全semantic fieldとcanonical化

* `kernel_type_codec.inc:5-18` はforall/lambda/letのbinder名だけをdepth由来のNameへ正規化し、domain/type/valueでは同じdepth、bodyだけdepth+1にする。de Bruijn indexを変更しない。app両側、projection子、metadata子を再帰し、metadataそのものは保持する。構造Expr＋depthでmemoizeするので、同一Exprが異なるbinder深度に現れても混同しない。
* `:20-49` はNameのanonymous/str/num構成と全Level constructor (`zero/succ/max/imax/param/mvar`) を保持する。`:51-57,91-108` は4種類のbinderInfo、全constant universe引数、bvar/fvar/mvar、sort、app、forall、lambda、letのtype/value/body/依存flag、projectionの構造名/index/子、nat/string literal、metadata参照を列挙し、項のpretty-printer省略を利用しない。
* `verify_run20.py:111-117` の `canonicalType == ci.type` は実際のExpr alpha比較であり、単なる文字列比較ではない。ただしLeanのalpha比較はbinder annotationを無視しうるため、この行だけではannotation保持の証明にならない。実装がbinderInfoをそのまま運び、元型とcanonical型の両方を構造codecへ通すこと、および以下の保存物独立比較がこの点を補っている。
* probeは全rowで元DAGをdepth canonical化した構造SHA256とexplicit DAGを比較した。共有node番号の差は意味に含めず、Name/Level、全引数、binderInfo、let flag、metadata snapshot値を含めた。**15,774件すべて一致**。bvar入替えをalpha名変更と誤認する経路はない。
* 保存original DAG 2,643,755 node、canonical DAG 2,646,175 node。originalにはlet 162、projection 1、metadata 990が実在する。binderInfoはdefault 90,553 / implicit 6,928 / strictImplicit 185 / instImplicit 11,807で、少数のstrictImplicit等も範囲に含まれる。

## PASS: DAG復元・参照・公理の自己依存

* `kernel_type_codec.inc:65-87,89-115` は実際に作ったJSON nodeを、すでに復元された子Exprだけからdecodeし、`ExprStructEq.beq` により元Exprと比較してからnodeを登録する。単なる元ExprのtoString比較ではない。子参照が常に既存 `restored` のindexであるため、生成DAG内のforward/self/cyclic参照は通らない。memoは標準mapの構造keyを使い、hash値だけを同一性と扱っていない。
* probeは両DAG全nodeのtag/arity、Name/Levelの形、child indexの整数性と `0 <= child < parent`、root範囲、binder code、let boolean、metadata参照範囲を独立検査し、違反0件だった。
* `verify_v06_alignment.py:183-197,240-250` は各宣言で実 `collectAxioms n` を取得し、許可 `{propext, Classical.choice, Quot.sound}` 以外と、自身をaxiom依存に持つ宣言を拒否する。`kind == axiom` という見かけだけでexport済proof stubを追加公理と判断しない。一方、本物の未証明axiomはcollectAxiomsに自身を含むので拒否される。`check_run20_guards.py:156-170` はisolated実axiomとconsumerを作る実Lean negative controlを定義し、継承 `check_run18_axiom_policy.py:15-47` はproved export stubの受理と実追加axiomの拒否を区別する。この監査人はcontrolsを再実行していない。
* 保存R03ではaxiom-kind row自体が0件（full private imports下でtheorem bodyが見える）。全rowの依存は許可3公理内、自己依存0。theorem 13,170、def 2,548、inductive 18、constructor 20、recursor 18。

## PASS: 旧公開型の同じcodecによる比較

`verify_run20.py:254-289` は固定BASE `07fe1ed...` のsourceを隔離し、**現行と同じ `audit_parts.py` → `audit_source` → `.inc`** で全base環境を取得する。replay全rowをgoldenと比較した後、`verify_v06_alignment.py:198-210` が各旧非private宣言のnormal `type` とcanonical `explicit_type` を比較する。privateは型不変比較から意図的に除外されるが、Run20側で全base名の存続を別途要求する。

保存base 1,003 module / 15,542 row。独立probeで保存base replayとgoldenの全row一致、全base名存続、旧公開11,928 rowのnormal型・canonical型一致を確認した。さらにverifierが比較keyへ含めていない `universe_parameters` も独立比較し、現保存証拠では全公開rowで一致した。一般には宣言universe parameter list単独の差をこの2-key比較だけで拒否する保証はないが、今回の旧source不変制約と実データの一致のもとで公開API退行を発見していない。

## 保証範囲の限界（今回のblocking findingではない）

1. **metadataは保存JSONのみからの独立復元ではない。** `kernel_type_codec.inc:84-86,104-112` は元の `Array MData` をdecodeへ渡す。`:118-121` の保存側は `reprStr d` の診断snapshotであり、その文字列を再decodeして同一MDataか検査する実装ではない。したがって「元のmetadataを保った実行中Exprの構造roundtrip」はあるが、「保存metadataを含む汎用self-contained JSON codecのroundtrip」は主張できない。保存実データは959 row / 990 entry、3種類のboolean markerのみ（noImplicitLambda 860 / borrowed 87 / noindex 43）で、元/canonical対応に欠落を見つけていない。metadataは数学的型のbinder・universe・定数引数を省略する代わりではなく、この制約は今回の数学的型保証を妨げない。docsの「診断snapshot」と整合するためblockingとしない。
2. **`decodeNode` は汎用の敵対的入力validatorではない。** childのforward/missing参照と不正tag/binderは拒否するが、Name/Level/node配列の余剰entryの厳密拒否、完成graph用の外部decoderや保存metadata parserはない。現在のencoderが生成したnodeを直ちに再構築する目的では全fieldを構造比較し、保存全nodeも独自probeの厳密arity検査を通過した。保存物の一般schema受理器としての堅牢性は保証しない。
3. **Python validatorはkernel checkerではない。** `verify_run20.py:154-156` とguards `:112-119` はkernel field/true flagの存在を確認するもので、保存文字列からLean Exprを復号してflagを再計算しない。信頼の根拠はsource-bound生成コードが実際のalpha/構造比較後にfieldを出す経路と実行記録である。この監査では保存物を追加の独立probeで照合したがfresh Leanを実行していない。
4. **controlsは全constructorの網羅的mutation testではない。** `check_kernel_type_encoding.py:18-54` はalpha名、bvar order、implicit/instance、universe、metadata、200段app、numeric Name、forward参照、共有memo等を検査する。strictImplicit/let/string/projection/全Level形の独立negative mutationを網羅しない。実装のexhaustive match読解と実存する保存nodeの全件検査を合わせて評価した。

MathのMain証明・50-ID意味対応、fresh cold実行、publication/ZIP bindingはcoordinator／別監査人の担当であり、この報告からそのPASSを導いていない。
