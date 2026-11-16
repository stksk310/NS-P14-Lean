# Block04 独立実装レビュー

2026年11月10日（JST）。実装者と別のレビュー担当が、Block04のソース・テスト・
検証スクリプトをV02 §7・§9、V03 III.1 O_LOW、実装計画と照合した。
確定ファイルのhashは同ディレクトリのmanifestに記録する。

判定：正しさに関する重大・軽微な指摘なし。

- 重みはV02 (7.3) と一致し、tailの添字j+2、分母j+k、rank 3第二行の8/3が正しい。
- rank 2には非負deficit・同じ列の総量・head≤2δだけを要求する。
  V=3、δ=0、両volume分岐、top行を含み、`Resources 2` の不要な制約は混入していない。
- rank 3の全3行は指定した総量とhead capから導かれ、多項式余裕と第二行の係数も原稿と一致する。
- `tail_vanish` が台の完全性を保証し、任意に遠い層も落とさない。
  budget・cap・rowは同じprofileを使う。Block03への射影は全層を保持する。
- 検証スクリプトは新規13定理の公理依存、既存回帰、監査の仮定検査、固定ソースhashを確認する。
  検証記録の8コマンドはすべて成功している。

レビュー担当が独立に `lake env lean tests/LowRank.lean` を実行し、終了コード0を確認した。
13件の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。

完成範囲はO_LOWの有限数値資源に対する重み付き和の評価である。
actual Tor上界、actual towerと各capの構成、target余裕・Betti移行、
実際のsourceに対するO_LOW全体を証明したとは扱わない。
