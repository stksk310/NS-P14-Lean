# Antipodal 短縮の監査・Lean 対応

読解対象：`origin/work` commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
既存 Lean、凍結契約、証跡は改変していない。以下の形式化済みという記載はこの SHA の実装を読んだ結果であり、今回 fresh Lean build を行ったという主張ではない。

## 採用した削減

厳密な \(Q_C\) 同定の代わりに、実商を張る有限候補語を構成して \(P_C\) の上界だけを取る。
第一 Betti 数には、この**実商自身**の調和上界を適用する。
候補商から実商への全射による Betti 数の単調性は使わない。
さらに最終の整数性を使う位置を調整し、\(h=4\) と \(h\ge5\) の分岐をなくした。
全 \(h\ge4\) で \(\beta_1\le B<A+1\)、\(A\in\mathbb Z\) を示せば \(\beta_1\le A\) で十分である。

| 元の節・補題 | 採用節・補題 | 操作 | 数学的理由 | 対応する Lean export | 新たに必要な形式化 | 状態 |
|---|---|---|---|---|---|---|
| V02 §13.5 (W25)、V03 (V.18) の厳密 presentation | APD.1 の候補語 | 主依存から削除・上界へ置換 | 三つの端点因子関係と次数 \(h\) 語の消滅で spanning が得られる。逆包含・線形独立性不要 | `NSP14.Endpoint.Data.antipodal_minimal_normal_form`; `antipodal_coreP_bound` (`Width/AntipodalCore.lean:189,262`) | 数学的内容は既存実装済み。紙の直接 spanning 証明をそのまま一つの商全射として export する必要はない | 紙上証明済み・Lean 形式化済み（同じ上界・異なる包装） |
| 厳密 \(P_C=\binom{h+1}2+1\) | APD.2 の \(P_C\le\binom{h+1}2+1\) | 強すぎる結論を削除 | 全候補語の生存性・単射を証明する必要がない | `antipodal_coreP_bound` | なし | 同上 |
| 厳密 \(W=h^2-h+2\) | APD.7 の一般 \(W\le u^2/4\) | 主依存から削除・共通評価へ統合 | \(R+u\le W\) と最終整数性で全 \(h\ge4\) の target を払える。第一行に \(u=8\) の尾和14は不要 | `NSP14.Endpoint.Data.wordVolume_quadratic_bound` (`Width/SparseVolume.lean:58`) | 上界自体は既存。統一された最終算術は次行参照 | 上界は紙上・Lean とも証明済み |
| 厳密 \(b_1(Q_C)=h+4\) | APD.6 の \(b_1\le2P_C/3+10/3\) | 主依存から削除・共通調和評価へ統合 | 三変数 Artin 商の一般評価で足りる | `NSP14.Endpoint.Data.QCore_first_third` (`Endpoint/CoreWeights.lean:26`) | なし。厳密 \(b_1=h+4\) は読解 SHA の一般 Lean 定理として未形式化であり、今回の主依存には入れない | 採用上界は紙上・Lean とも証明済み |
| W25 から第一行を払う差 \((h^2+h-12)/2\)、および既存 Lean の \(h=4\)/\(h\ge5\) 分岐 | APD.2 の全 \(h\ge4\) に一つの算術 | 置換・分岐削減 | \(A+1-B=[(h-4)^2+9(h-4)+2]/6>0\) と整数性で十分。第一行の exact tail 基点を削除 | `NSP14.Endpoint.Data.actual_antipodal_first` (`Width/AntipodalComparison.lean:74`) は同じ結論を既存の分岐付き証明で供給 | **新しい統一算術そのものの Lean export は未追加**。下記の正確な statement と既存入力から後で実装可能 | 新しい統一経路は紙上証明済み・Lean 未形式化。同じ最終比較の既存形式化は保持 |
| antipodal/non-antipodal の高次行 | 幅章の全構造共通評価 APD.9 | 統合 | 四点集合の分類は第一行にしか要らない | `NSP14.Endpoint.Data.actual_five_higher` (`Width/FiveHigher.lean:49`) | なし | 紙上・Lean とも証明済み |
| 個別の元 source・physical target 接続 | 本稿共通接続補題 | 共通化 | 正規化は元の \(G\) と同じ polynomial action を保持し、\(u\le V\) と target 容量単調性を一度適用 | `NSP14.NumericalSemigroup.narrow_five_large_comparison` (`Width/AntipodalComparison.lean:133`); `narrow_five_comparison` | 共通 wrapper の追加 export は任意。個々の結論は実装済み | 紙上証明済み・Lean 個別接続済み |

「主依存から削除」は既存ファイルの削除を意味しない。厳密 presentation などを付録に移して必須にしたのでもない。
それらを全て読まなくても本稿のこの分岐を検証できるという、数学的仕事そのものの削減である。

## 依存の実コード検査

`public import` / `import` を再帰的に走査し、次を確認した。

| 起点 | 到達する antipodal 関連モジュール | 到達しない独立成果 |
|---|---|---|
| `NSP14.Width.AntipodalComparison` | `Additive.CyclicAntipodal`, `Width.AntipodalCore`, `Width.FiveNonAntipodal`, 起点自身 | `Width.AntipodalBasis`, `AntipodalPresentation`, `AntipodalIdeal`, `AntipodalVolume` |
| `NSP14.Width.FiveComparison` | 同上 | 同上 |
| `NSP14.Width.Closure` | 同上 | 同上 |

実際の短い鎖は
`AntipodalCore.antipodal_coreP_bound → AntipodalComparison.actual_antipodal_first → narrow_five_large_comparison → FiveComparison.narrow_five_comparison → Closure.narrow_width_comparison`
である。高次行は `FiveHigher.actual_five_higher` から入る。

この実コードの `actual_antipodal_first` は \(h=4\) で `five_wordVolume_eight` を使う既存証明である。
今回採用した紙上 APD.2 は、その**同じ結論**を一般二次評価と整数性だけで証明する新しい経路であり、既存コードを変更していない。
従って import 検査の結果を、新しい単一算術の Lean 実装が済んだという証拠にはしない。

集約 import ファイル `NSP14.lean` は独立成果も全て公開している。この import 上の同居を数学的依存と混同しない。
宣言名を `NSP14/` 全体で検索すると、`AntipodalBasis` の厳密生存性は `AntipodalPresentation`、`AntipodalVolume` だけ、
`AntipodalPresentation` の厳密商同型は `AntipodalIdeal` だけで参照される。
`AntipodalIdeal` と `AntipodalVolume` の公開宣言は他の本番 `NSP14/` モジュールから参照されない。
このため、この四モジュールの厳密成果を幅比較の主依存から外しても、別の幅枝から入り直す辺はない。
これは静的 import/名前参照の確認であり、今回 kernel の `collectAxioms` を再実行したという意味ではない。

## 保持した境界・入力

- 任意標数：端点因子関係の係数は1。調和評価の有理数は次元の重み。標数間の rank 一致を仮定しない。
- \(\gcd(t,h)=1\) は分類の帰結であり、\(\gcd(t,2h)=1\) への強化をしない。APD.1–2 の上界自身は前者さえ使わない。
- \(h=4\) でも一般二次上界 \(W\le16\) から \(\beta_1\le89/3<30\) が得られ、整数性で容量29を払える。\(B\le A\) という不要に強い実数不等式を求めない。
- 全 \(h\ge4\) の差 \(A+1-B\) は \(h=4\) で \(1/3\)、以後も非負係数多項式で正。これが厳密な整数閾値を保証する。
- \(u=8\) の尾和 \(W\le14\) は第一行の主依存から外す。ただし全構造共通の第2行を扱う `FiveHigher.actual_five_higher` の基点には引き続き必要なので、全証明から削除したとはしない。
- \(R\) は元の actual \(H_2(x,v;G)\)。\(R\) と \(\widehat R\) の等式、\(P_C=P_G\)、反射による source 保存は仮定しない。
- \(m\ge du+2\) の最小境界、\(d=1\)、\(i=0\)、\(i=5\)、\(i>5\) は共通端点/target 接続と全構造共通高次行に委ねる。APD.5 は第一行だけを正確に主張する。
- 候補語を数えただけなので、その単射・厳密 Hilbert 関数・厳密 generator 数は主張しない。

## 新しい統一算術の形式化用 statement

新しい補題として実装するなら、\(h,n\in\mathbb N\) に対し
\[
 h\ge4,\qquad 6n+7h\le11h^2+30
 \quad\Longrightarrow\quad n\le\binom{2h}{2}+1
 \tag{U-APD}
\]
という加法形が飽和減算を避ける正確な契約になる。仮定は APD.2 の既存入力から得られる。
実際、結論を否定すると \(n\ge2h^2-h+2\) なので
\(6n+7h\ge12h^2+h+12\)。仮定と比較すれば \(h^2+h\le18\) となるが、
\(h\ge4\) なら \(h^2+h\ge20\) で矛盾する。この補題は紙上証明済みであり、対応する新しい Lean export は今回追加していない。

初回の短縮案では \(h=4\) の尾和14を第一行に残したが、独立レビューで上の整数閾値による統一を確認し、採用本文を置換した。
旧案の『\(89/3>29\) なので尾和が必要』という判断は、最終整数性で十分なことを見落としていたため撤回する。

## 長さの評価に関する注意

旧 V02 は厳密 presentation と三つの厳密式を既に短い段落に圧縮していた。
その段落の文字数との差だけからページ削減を算定すると、独立性・距離の最短性・正確な Betti 計数に要する監査を落としてしまう。
ここで除いたのはそれらの数学的証明義務であり、レイアウト条件を固定した組版前に「何ページ減」とは断定しない。
本稿 APD.1–2 は必要な端点消滅式と全 \(h\) の容量差を展開しているので、そのまま通常本文へ組み込める。
