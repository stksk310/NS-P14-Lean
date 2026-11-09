# NS-P14-Lean

NS-P14のLean形式化。

## 状態

Block01「小rankのscalar評価」の数値部分をコンパイル・独立監査済み。
恒等式は全有理数シフトについて、正値性は非負整数シフトについて証明している。
rank 6–8では基点 `(s,t) = (0,0)` の除外条件が必要。

actual Apéry–Sidon、資源上界との接続、Bettiへの移行、M12・P14全体は未完了。

- [Lean証明](NSP14/Ordinary/SmallScalar.lean)
- [元の検証記録](verification/block01/verification.json)
- [独立監査の要約](audit/README_JA.md)
- [独立監査の機械可読記録](audit/review.json)
- [進捗](LEAN_PROGRESS.md)

## 検証

Leanとmathlibの版は `lean-toolchain` と `lake-manifest.json` に固定している。
固定版のLean/Lakeと依存ライブラリを用意して、次を実行する。

```sh
lake build
lake env lean NSP14/Ordinary/SmallScalar.lean
lake env lean tests/SmallScalar.lean
lake env lean audit/DomainChecks.lean
```
