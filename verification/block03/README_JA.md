# Block03：同じ資源列からSO3上界を証明

2026年11月9日（JST）。ソースは [Resources.lean](../../NSP14/Ordinary/Resources.lean)。
固定Lean・mathlib revisionは変更していない。

## 完成した範囲

`Resources r e d` の資源から、`4 ≤ r`、`r ≤ n` の任意の整数cutoffについて
`Resources.scalar_le_upper` がSO3を証明する。
これまでの受入口で仮定していた `F ≤ upper …` を、この定理では資源の条件から導く。

| 紙上の量・条件 | Leanでの表示 |
|---|---|
| H₀=δ | パラメータ `d`（狭幅側のdilationではない） |
| H₁ | `R.head` |
| H_{j+2} | `R.tail j` |
| 有限な台 | `R.support`、台外ゼロの `R.tail_vanish` |
| H₁,H_{j+2}≥0 | `head_nonneg`、`tail_nonneg` |
| δ+H₁+ΣH_{j+2}≤δV | `budget` |
| H₁≤e+δ−1−a_r | `head_cap` |
| H_{j+2}≤e+δ−1 | `tail_cap` |

SO3自体にはδの非負性やeの下限は不要なので、構造体に重複して要求していない。
SO5への接続では `e=r+1+s`、`δ=a_r+t`、`s,t : ℕ` を用いる。
資源の台はcutoff以下に制限していない。任意に大きい添字も許す。

## 紙上式との対応

参照：`auditability_search/ORDINARY_PAPER_REDUCTION_JA.md` §2 (SO3)、§3 (SO5)。
`R.scalar` は同節の

F_r=(r−1)δ+(r+1)H₁/2+Σ_{t≥2}(r−1)H_t/(t+1)

を有限台上で定義する。`j=t−2` のため、Leanの分母は `j+3`。
α=(r−1)/(n+1)を各重みから引き、総量のα倍を分離する。
残余重みは `j<n−2` で非負、`j≥n−2` で非正となる。
後者を落とし、前者を共通capで評価し、台にない添字を非負項で埋める。
この有限和評価が `residual_tail_le`、総量とhead capも合わせた式がSO3である。
同じ `R` の総量・head・tailを使い、別のprofileの上界を組み合わせていない。

`Resources.scalar_lt` はBlock01の角条件を受けてSO5へ進む。
`Resources.scalar_lt_of_boundary_sidon` と `Resources.scalar_lt_of_apery_pairs` は
Block02を合成し、境界のSidon証拠または数値Apéry-pair証拠からその角条件を導く。
いずれも `F ≤ upper` を追加の仮定として要求しない。

## 検証

```sh
python3 scripts/verify_block03.py
```

このクラウドの固定環境では `PATH=/tmp/ns-p14-lean/bin:$PATH` を先頭に付ける。
build、ソース再検査、Block03のテスト、Block01・02の回帰テスト、
監査の負のシフト検査を実行する。新規7定理と従来10件・14件の公理依存を検査し、
`propext`・`Classical.choice`・`Quot.sound` 以外を拒否する。
Block03では件数に加えて、監査する7定理の完全名も照合する。
前二ブロックの証明ソース・テストおよび固定環境のhashを既存manifestと照合する。

テストは空のtail、任意の添字に置かれた非零層、cutoffの直前・一致・直後の符号、
普遍的なSO3・SO5の受入口、二つの境界接続、証拠が不要な内部点を含む。
数値例は普遍証明の代わりではなく、添字・接続の回帰検査である。
`interface_before.log` は実装前に公開インターフェースが存在しなかった確認記録。

このディレクトリのmanifestがBlock03を含むスナップショットの照合対象。
Block01・02の各manifest・ログは監査修正時点までの履歴として保持し、
今回の公開import追加で変わるroot `NSP14.lean` の過去hashを書き換えない。
今回の前二ブロックの再検証結果はこのディレクトリの回帰ログに保存する。

## 未完の接続

実際の半群・接錐・一つのcut・towerから、上記すべての条件を同時に満たす
`Resources` を構成する部分は未実装。構造体のフィールドは明示した入力である。
また、actual Q₂の最大性から `AperyPairData` を構成する橋、
r=2,3およびr≥9のscalar閉鎖、Tor/Betti、M12全体・P14全体は未完である。
今回の完成範囲は資源を入力とするSO3と小rank数値閉鎖との接続である。
