# NS P14 V06 公開本文と監査用の入口

V06 の紙上証明と、既存 Lean に合わせるための引継ぎ資料を公開する。Lean の証明コード・凍結契約・既存検証証跡は変更しない。

## 監査スレで読む場所

- [N4 章全文](../proof_sharp_v6/chapters/05_N4_JA.md)：N0 の仮定から N8 の被覆まで。
- [V06 全体本文](../proof_sharp_v6/NS_P14_SHARP_PROOF_JA.md)：共通容量、共通端点、ordinary、幅比較、N4、最終合成を含む。
- [V06 PDF](../proof_sharp_v6/build/NS_P14_SHARP_PROOF_JA.pdf) と [V06 ZIP](../proof_sharp_v6/NS_P14_SHARP_V06.zip)。
- [N4 の変更・Lean 対応監査](../proof_sharp_v6/notes/N4_AUDIT_JA.md)。
- [V06 への Lean 経路同期指示](../lean_alignment_v06_handoff/EXECUTION_PROMPT_JA.md)。この指示の対象に N4／Run19 は含めていない。

N4 の新 cubic は N4b、actual 上界は N1b・N4a、その支払いと区間補完への接続は N4c の直後にある。u=3,4,5 の高次行は同節の表、第一行は N5–N7、全域の被覆は N8 に記す。章だけを切り出して確認する際も、全体本文の共通容量と共通端点の入力を併読すること。

ここでの N4 は**紙上証明**である。新 cubic の Lean 補題、標準語長・元の height への N4 固有接続、actual N4 全域 consumer は未形式化部分を含む。既存 `actual_two_row_one/two/three/four` 等の形式化済み入力や Run18 六契約 COMPLETE と、N4 全域・全 P14 の Lean 完了は区別する。

N4 章は V04・V05・V06 で同じ内容で、SHA256 は `cd6236f6b16d5de7998064e66d566f5c6522c8a943d040ec6242a18dde2194c5`。V06 で変更されたのは端点章と幅比較章である。

## 公開物と歴史的記録

V04・V05・V06 の本文・台帳・レビュー・既存 ZIP と、README から参照する最終 PDF を保存する。各版の receipt と ZIP は作成時の原本のまま保持する。内部の `published_to_remote: false` やローカル作業ブランチ名は、原本作成時点の記録である。公開された版は、この案内と原稿を含む Git コミットで特定する。

通常の Git ツリーには一時的な aux／log／失敗した組版 draft を追加しない。旧検証器が厳密な過去ファイル集合として照合する組版証跡は、[FROZEN_TYPESETTING_EVIDENCE.zip](FROZEN_TYPESETTING_EVIDENCE.zip) に固定保存した。これは過去記録の復元用であり、新しい数学的認証ではない。V06 の失敗した `draft_overfull` は配布対象から除外した。

[PUBLICATION_MANIFEST_SHA256.json](PUBLICATION_MANIFEST_SHA256.json) が公開ファイルの bytes を、[publication_validation.json](publication_validation.json) が今回の公開前点検の範囲を記録する。旧 Run18 の Lean 検証を新しく実行したとは扱わない。

## 算術検査と原本保全検査

公開 checkout で、原稿の式と境界の算術検査だけを実行するには次を使う。Python の `sympy` が必要である。

```sh
python3 -B proof_sharp_v6/checks/verify_reduction.py --math-only
```

旧検証器の既定モードには、未追跡の原稿を作成した当時の BASE に対して `git diff` が空である、というガードもある。公開後の checkout でそのまま実行すると、原稿を追加した Git 差分を検出する。このガードや過去の検証器を弱めず、原本保全検査は次のように**元の BASE の別 checkout に、公開原稿を未追跡資料として展開して**再現する。`pdfinfo` と `sympy` が必要で、Lean のコンパイルは行わない。

公開コミットを checkout したリポジトリの root から実行する。浅い clone で元の BASE が未取得なら、先に `git fetch origin 345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` で取得する。

```python
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys
import tempfile
import zipfile

repo = Path.cwd()
check = Path(tempfile.mkdtemp(prefix="ns-p14-v06-paper-audit-"))
base = "345e2d82fea50ef89e00a8f35c4fb53ac601d7ce"
subprocess.run(["git", "worktree", "add", "--detach", str(check), base], check=True)
paths = ["proof_sharp_v4", "proof_sharp_v5", "proof_sharp_v6",
         "lean_alignment_v06_handoff", "proof_sharp_publication"]
payload = subprocess.check_output(["git", "archive", "HEAD", *paths])
subprocess.run(["tar", "-x", "-C", str(check)], input=payload, check=True)
manifest = json.loads((check / paths[-1] / "PUBLICATION_MANIFEST_SHA256.json").read_text())
for name, expected in manifest.items():
    assert hashlib.sha256((check / name).read_bytes()).hexdigest() == expected, name
with zipfile.ZipFile(check / paths[-1] / "FROZEN_TYPESETTING_EVIDENCE.zip") as z:
    assert z.testzip() is None
    for name in z.namelist():
        p = PurePosixPath(name)
        assert not p.is_absolute() and ".." not in p.parts
        assert p.parts[0] in paths[:3] and p.parts[1] == "build"
        assert not (check / name).exists(), name
        z.extract(name, check)
subprocess.run([sys.executable, "-B", "proof_sharp_v6/checks/verify_reduction.py"],
               cwd=check, check=True)
print("Original paper snapshot checked in", check)
```

この検査は恒等式・有限転記・PDF 頁数・旧資料の bytes と被覆の点検であり、全称命題の証明や新経路の Lean 認証の代用ではない。
