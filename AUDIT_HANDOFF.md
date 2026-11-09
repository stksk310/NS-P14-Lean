# Lean Block01・02 監査引継ぎ

2026年11月9日（JST）。このスナップショットは `work` ブランチで公開する。

## 最初に読むもの

1. [現在のLean化進捗](LEAN_PROGRESS.md)
2. [Block01：small scalar](NSP14/Ordinary/SmallScalar.lean)
3. [Block02：Sidon・数値Apéry・scalar接続](NSP14/Combinatorics/Sidon.lean)
4. [Block01の範囲](verification/block01/README_JA.md) と [Block02の範囲](verification/block02/README_JA.md)
5. [V03骨子](proof_structure_v3/P14_PROOF_SKELETON_V03_JA.md) と [依存表](proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)

## 特に確認してほしい境界

- 全整数シフトに対する恒等式・正値性であり、数値サンプルからの外挿ではない。
- rank6–8の悪い角ではgapが負になることもテストしている。
- Sidon性は同じ項の反復を含む二項和の一意性。差の単射は合成数・偶数のmodulusを許す。
- `AperyPairData` は加法部分モノイドの数値最小元・二項和の最小性・和の一意性を明示した入力。
  actual Q₂の最大性からこのデータを構成する代数的な橋は未実装。
- 境界版のSidon証拠はr≥6かつs=0だけで要求する。内部点へ不要な仮定を加えない。
- SO3資源上界、actual接錐・Tor/Bettiへの接続、P14全体のLean証明は未完成。

## 再現

Lean `v4.36.0-rc2` とmathlib revisionはtoolchain・Lake manifestに固定してある。
標準のelanを利用できる環境で、リポジトリrootから実行する。

```sh
lake build
python3 scripts/verify_block02.py
```

Block02の検証スクリプトは新ソースの再検査・テスト・14個の公理依存報告と、
Block01の回帰テスト・10個の公理依存報告を検査する。
通常のLean基盤 `propext`, `Classical.choice`, `Quot.sound` 以外の依存を拒否する。
追加の数学公理や `sorryAx` への依存は認めない。

mathlibキャッシュ先へのアクセスが制限される環境では、初回のみ次で依存を取得し、ソースビルドする。

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
```

このクラウドでは公式GitHub配布の固定Leanを `/tmp/ns-p14-lean` に導入した。
同じ環境なら次で実行できる。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block02.py
```

[保存済みBlock02検証記録](verification/block02/verification.json) とログを同梱する。
ローカルで再検証すると所要秒などは更新されるため、厳密な比較対象には監査するコミットを指定する。

## 同梱資料

V03、旧証明、二つの紙上置換、Navi別証明、Lean化計画、対応ZIPを保存している。
旧資料があることは現Lean証明の依存にそれらを公理として足すことを意味しない。
コンパイラ本体、`.lake`、生成された`.olean`、Pythonキャッシュ、接続設定や資格情報は含めない。
V03骨子ビルダーの入力指定文は元の添付パスを参照する。必要なら同梱V03 ZIPから元の相対位置へ復元する。
Leanのbuild・検証はその添付指定文に依存しない。
