# N4章の変更・形式化・検証台帳

対象 commit：`345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
本章は同 commit の V03、V02 §14、N4 置換稿、後半可読性監査を読んで統合した。
既存ファイル・本番 Lean・凍結命題・証跡は変更していない。

## 採用した実削減

N4 高次行の支払いでは、旧 N16–N18 の三次・四次・五次式を、
新 N4 の一つの三次式と二つの二項係数比へ置き換えた。
四次・五次の恒等式そのものと、第2行の補正容量 \(+V\) が不要である。
付録移動による見かけの削減ではない。使用条件は \(u\ge6\)、小幅は明示して残した。

新補題の正確な statement は次である。

> \(u\in\mathbb Z,\ u\ge6\)、\(U_2=5u^2/4-2u+4\)、
> \(U_3=u^2-3u+4\)、\(U_4=u^2/4-u+1\) と置くと、
> \(U_i\le i\binom u{i+1}\) が \(i=2,3,4\) について成立する。

証明は本文 N4b–c に全て記した。この補題の入力は整数幅だけであり、
体や actual source の構成を追加仮定にしていない。
新規 Lean 実装を行っていないので「紙上証明済み・Lean未形式化」に分類する。

## 変更対応

|元の節・補題|採用箇所|操作|数学的理由|対応 Lean export|新形式化・状態|
|---|---|---|---|---|---|
|V02 N4–N5 / V03 E_TWO|N1|共通章へ整理|実核補償後の二変数四行だけを使用|`NSP14.Endpoint.Data.actual_two_row_one/two/three/four`、`completed_two_all_rows`|四行は形式化済み。本章固有の全域合成とは区別|
|V02 N6–N9 / V03 N_DISTANCE|N2|統合・保持|三点 Kneser と socle 三角形包含は必要|`NSP14.Additive.threePoint_growth`、`threePoint_coprime_growth`、`NSP14.Endpoint.Data.internalSigma_point_count`|三点 growth・socle 基底は形式化済み。N4 の実 downset/三角形への接続は未形式化|
|V02 N10–N13 / V03 N_WORDS|N3|統合・保持|SC unit の整数 offset への帰還と元の height を明示|`NSP14.Additive.savchevChen_twoValue`、`normalized_modular_relation`、`NSP14.Endpoint.Data.actualR_le_height`|SC consumer は形式化済み、標準語長・N4 height への固有接続は未形式化|
|V02 N14–N18 / V03 N_HIGH|N4|置換・実削減|第2行 cubic が他の高次行を支払う|`NSP14.Endpoint.Data.actual_two_row_two/three/four`|新数値補題と実 target consumer は未形式化、紙上証明済み|
|N4置換稿 P3–P7 / V03 N_FIRST|N5|統合・保持|三関係と一括三角計数で全幅9以上を閉じる|N4 専用 export は対象 commit に存在しない|紙上証明済み・未形式化|
|N4置換稿 §§3–6 / V03 N_SMALL|N6|統合・保持|幅6–8と3/4の短い包含だけを残す|N4 専用 export は対象 commit に存在しない|紙上証明済み・未形式化|
|V02 N23–N28 / V03 N_WIDTH4|N7|保持・監査用に展開|全競合、両座標、非禁止像の独立が必要|N4 幅4専用 export は対象 commit に存在しない|紙上証明済み・未形式化|
|旧196組 core 証書|主依存から除外を継承|削除を再導入しない|N5–N7が全パラメータを紙上で覆う|なし|V03で既に除外済み、本改稿の新削減には算入しない|

対象 commit に `NSP14/NarrowFour/` の本番実装は存在しない。
`docs/superpowers/plans/2026-11-15-run19-n4-small-closure-order.md` は実行計画であり、
そこに記載された export 候補を既存形式化済み定理とは数えない。
Run18 COMPLETE は四生成元の全域 Lean 完成を意味しない。

## 依存分類

- A（核心）：三点 Kneser、SC の元 offset への帰還、socle 三角形包含、三関係計数、
  幅6–8の包含、幅4の全競合と像の独立性、actual 核の補償付き四行。
- B（共通接続）：完備/代数接錐の Betti 同一性、物理幅 \(du\)、actual target 容量、
  第0行・source 消滅行は全体の共通章へ。
- C（不要な強さ/別経路）：旧四次・五次支払いの恒等式と第2行の \(+V\) 補正。
  core の exact 値、actual \(R\) の exact corner 計算、196組証書は本章に不要。

## 検証した境界

\(u=3,4,5\) は大幅の三次式へ混ぜず保持した。
\(u=4,V=4\) の target 最小列は第2–4行 \((12,7,1)\) であり、
source 第4行の上界0を支払う。旧稿の説明で source の0と target 自身の上端を混同しない。
幅4で \(m=6\) を独立処理し、\(m>6\) の4剰余は全商 \(Q\) を覆う。
\(E_h(k_0)\) は guard 付きで定義し、Nat の飽和減算を無条件の二項係数へ変換していない。
二項係数比で割る分母は \(u\ge6\) で正、係数体での除法ではない。

新しい数値恒等式は 2026-11-15 に Python/SymPy で独立に展開し、
\(12(T_2-U_2)|_{u=6+z}=4z^3+45z^2+140z+36\)、
\(U_2-U_3=u^2/4+u\)、\(U_2-5U_4=3u-1\) を確認した。
これは転記照合であり、全称性の根拠は本文の恒等式・正係数・比の不等式である。
Lean/lake は本章担当では再実行していない。

## 未確定案

採用した補題に未証明案は混ぜていない。
幅4を一般の下界 \(L_1(4)=7\) だけで払う案は採らなかった。
\(m\equiv1,2\pmod4\) の生成元上界8には actual 剰余容量10,9が必要である。
新 N4 数値補題以外の N4 固有核心は既存の紙上ルートを保持したため、
この章単独の新しい実削減は高次支払いの二つの高次多項式の除去に限定する。
