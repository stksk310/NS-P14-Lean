# P14 証明構造 V03

今回は完全論文・全文改稿の前に、証明の骨子と必要依存を固定した。
旧稿・旧証書を保存し、主証明に採る経路だけを一本にした。

読む順序は次のとおり。

1. [数学的に精密な六Partの骨子](P14_PROOF_SKELETON_V03_JA.md)
2. [全50補題・公刊入力の完全依存表](P14_DEPENDENCY_MAP_V03.md)
3. [V02全17節の置換・保存台帳](P14_PROOF_REPLACEMENT_LEDGER_V03.md)
4. [査読準備・残る監査とLeanの範囲](P14_REFEREE_READINESS_V03.md)

ordinaryはApéry–Sidon＋同じcutのscalar、N4は紙上置換を採用する。
旧第15節、196組証書、83組・665比較・5tail、Naviのlex別証明を主依存から外す。
公刊入力、共通代数、幅6–8の場合分け、幅4の全multiplicity、高次行は保持する。

lemma_registry.json は全補題の量化・仮定・直接依存・証明の核心・出典・入力種別・標数・監査限界を記録する。
COVERAGE_V03.json は全領域への接続を記録する。
[独立レビュー](audits/INDEPENDENT_ARCHITECTURE_REVIEW.md) は構造固定PASS、未解決指摘0。
これは外部専門査読やLean kernel認証ではない。

## 再現

ZIPを展開したroot、又は元のworkspace rootで実行する。
次は骨子・依存表をworkの確定断片とregistryから再生成し、構造を照合する。

~~~sh
python3 -B proof_structure_v3/checks/build_and_check_structure.py
~~~

この検査は出典同一性、DAG、参照、区間の転記、数式区切りを検査する。
補題の数学的真偽を自動判定するものではない。
出典ファイルと今回の構成指定文も同梱し、同一の相対位置へ展開する。

今回一回ずつ観測した算術検算は次の3本で、結果をauditsへ保存した。

~~~sh
python3 -B auditability_search/ordinary/verify_ordinary_reduction.py
python3 -B proof_integrated_v2/checks/verify_scalar.py
python3 -B proof_integrated_v2/checks/verify_width.py
~~~

large scalar checkerには旧rank4–8と補助診断も含まれるが、それらを主定理の前提へ戻してはいない。
旧196組・83組の列挙を今回の主ルートのために再実行していない。
SOURCE_RECEIPT.jsonが保存済み4package・48memberの同一性を記録する。

work/は骨子の確定した部品であり、代替証明を追加した主ルートではない。
構造検査を再現するため保存する。新しい全文執筆は今回の成果に含めない。
