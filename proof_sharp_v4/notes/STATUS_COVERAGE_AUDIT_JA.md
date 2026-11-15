# 最新状態・全域 coverage・共通接続の独立監査

対象リポジトリの読解 SHA は `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` (`origin/work`)。
本監査は status の現在欄、実宣言の型・証明ソース、保存済み証跡と Git blob の読み取りに基づく。
Lean/build/checker の再実行、旧指令書の実行、既存証跡の書換えは行っていない。

## 1 結論：Run18 COMPLETE と全域主定理の形式化を分ける

最新 `docs/RUN18_CLOSURE_STATUS.json` の現在欄は
`COMPLETE_ALL_SIX_PROOFS_COLD_VALIDATION_AND_REVIEW`、`run18_complete=true`、
`closed_ids=[W_SPARSE,W_FIVE,W_EDGE,X_BHP_EK,W_DENSE,W_CLOSE]`、`unproved_ids=[]`。
これは保存された閉鎖定理、R16 検証、独立レビュー、公開 receipt と一致する。
同じ JSON 内の過去の PARTIAL 欄や Run19 計画作成時の古い Run18 状態を、現在の未完欄として読まない。

ただし、`W_CLOSE` の元の型は次である。
\[
 \forall S,k\ [\operatorname{Field}k],\quad
 e(S)\ge5\ \land\ w(S)\le m(S)-2
 \Longrightarrow\forall i\in\mathbb N,\quad
 \beta_i(G_S;k)\le\beta_i(G_{\widetilde S};k).
\]
`audit/run18/RequestedGoals.lean:71` と `NSP14/Width/Closure.lean:16` を直接確認した。
これは**五生成元以上の狭幅全域**の型であり、小生成元と四生成元の狭幅を含む全域主定理の型ではない。
`audit/run18/ClosedGoals.lean:16` の `all_closed` はこの Run18 六契約の論理積である。

この SHA には `NSP14/NarrowFour/`、`NSP14/SmallEmbedding/`、`audit/run19/`、`verification/run19/`、
`docs/RUN19_CLOSURE_STATUS.json`、`docs/RUN20_CLOSURE_STATUS.json` が存在しない。
本番・監査の宣言検索でも、計画された Run19 十契約の閉鎖 wrapper と全域 P14 の最終合成 export は見つからない。
したがって、**Run19/20 の要求する実対象に対する全域閉鎖 export は、この SHA では未実装**である。
これは共有基礎や個々の小生成元算術まで未形式化という意味ではない。

| 範囲 | この SHA で読める実出口 | 判定 |
|---|---|---|
| ordinary、\(e\ge3,w\ge m-1\)、任意体・全行 | `NSP14.Ordinary.ordinary_actual_completion_betti_le` (`Ordinary/Closure.lean:16`) | 形式化済み。元の完成接錐と literal target、各最小変数列を持つ |
| 一般端点模型・元 source への輸送・実核補償・全行 | Run16 閉鎖と `Endpoint/FullTransfer.lean`, `Endpoint/Normalization.lean:20` | 形式化済み。N4 固有の全域比較そのものとは区別 |
| Kneser/SC とその一般 consumer | Run17 `COMPLETE` | 形式化済み。SC を使った N4 固有の全標準語・全幅比較の完了までは含めない |
| \(e\ge5,w\le m-2\)、任意体・全行 | `NSP14.NumericalSemigroup.narrow_width_comparison` (`Width/Closure.lean:16`) | Run18 として形式化・保存検証済み |
| \(e=4,w\le m-2\) の全幅 | 紙上 N4 証明、Run16 の二内部変数・socle・行評価、Run19 の実装計画 | 全比較の閉鎖 export は未実装 |
| \(e=1,2\) の全 source/target 接続、\(e=3\) の LTV による全幅 | 紙上証明・公刊入力。一般 AP/二生成元などの既存実装あり | Run19 `I_BASE/X_LTV/I_THREE` の要求する閉鎖 export は未実装 |
| 排他的全域分割から MAIN | 紙上合成。Run20 の担当として計画されている | 全域 Lean 主定理 export は未実装 |

`docs/superpowers/plans/2026-11-15-run19-n4-small-closure-order.md` の担当十 ID は
`N_DISTANCE,N_WORDS,N_HIGH,N_FIRST,N_SMALL,N_WIDTH4,N_CLOSE,I_BASE,X_LTV,I_THREE`。
ここで挙げた計画は現状を区別するために読んだもので、今回の作業として実行していない。

## 2 保存された COMPLETE 証跡の結合

現在欄が指すのは `verification/run18/runs/release_candidate_20261115_r16/verification.json`。
記録された 280 command は全て `passed=true` かつ `exit_code=0`、268 fixture、10,662 environment declaration、
うち新規2,421、`expected_open_acceptances=[]`、全六 ID 閉鎖、未証明 ID なしである。
許容公理の記録は `propext,Classical.choice,Quot.sound` のみ。
fresh project/test/new-production cache が使われたという過去実行の記録を確認したが、本監査で再実行したとはしない。

独立報告 `verification/run18/complete_review_20261115.md` は全六契約を PASS とし、
Critical/Important/Minor は0、pending/declined/remaining は空である。
`review_snapshot_complete_20261115.json` の報告 hash と検証 hash は実ファイルの再計算値と一致した。
同報告は数学ソースレビューと保存検証照合の範囲を明示し、reviewer が二度目の Lean build をしていないことも明示している。

本監査では以下を**新たに読み取り検査**した。

| 検査 | 今回確認した結果 |
|---|---|
| `SOURCE_SHA256.json` の全2,033 entry と現在 bytes | 全一致 |
| 同2,033 entry と凍結 proof source `a5f480c5136042597fceae23ad06d2ef3923ed02` の Git blob | 全一致 |
| `MANIFEST_SHA256.json` の全297 evidence entry と現在 bytes | 全一致 |
| R16 `verification.json` の各 command 結果 | 280件全て記録上 PASS / exit0 |
| COMPLETE ZIP | 実在、4,580,933 bytes、2,338 entry、全 CRC 合格、receipt の SHA256 と一致 |

主要 hash は次のとおり。

| ファイル | SHA256 |
|---|---|
| R16 `verification.json` | `99b1c1d68b87d1e39bb94bfe93aa4a0d7ccd6fac8097f588c5a3722ac600c557` |
| R16 `SOURCE_SHA256.json` | `5b9b0ca17bcb02600b6028d1b184cb671524743c79226e3f69a1c98e6b421537` |
| R16 `MANIFEST_SHA256.json` | `1c5decbddcb9100223dfd9332dcdcf2d757b8240f7a6635b2abb2f3543b8d0d6` |
| `complete_review_20261115.md` | `118131fb3151fdfbec20a175344114c67831dcdecf686dc758ea8fb977447df9` |
| `review_snapshot_complete_20261115.json` | `4594101c10a566c12d8412334acd85a7f1dbd290a530ac132e40ae2698e1f282` |
| `artifacts/NS_P14_LEAN_RUN18_COMPLETE_20261115.zip` | `1acfe35915b20c4c870a148a6a39d833a1f796de4f62f3f83ba280ca894c774d` |

`complete_publication_receipt_20261115.json` の公開入力対象は
`reviewed_commit=c97fa324d90277bcae20a88863366bff6ba7a35b`、同じ凍結数学 source である。
receipt と ZIP の一致は Run18 の公開束の同一性を支持する。
その束には依存リポジトリを含む全 checkout が入るという主張はなく、再現には固定 Git checkout と依存が必要である。
新稿全体の形式検証や原典全文の再査読を、これらの hash 検査から結論しない。

## 3 全パラメータ・全行の coverage

数学的全域分割は以下で尽くされる。ここで「紙上経路」は採用本文の証明であり、
同じ範囲の Lean 閉鎖 export が存在するかは §1 の別欄で判定する。

| 全域からの分岐 | さらに必要な分割 | 覆う行・境界 |
|---|---|---|
| \(e=1\) | 数値半群は \(\mathbb N\)、source=target | 全行。幅0、offset の空 gcd、\(v=0\) の式を使わない |
| \(e=2\) | \(G\simeq k[X,Y]/(Y^m)\) | \((1,1,0,\ldots)\)。target 第一行非零、source 消滅後の target 消滅は不要 |
| \(e=3\) | LTV の任意体全幅比較 | 理想/商の添字換算、第0行を補う |
| \(e\ge4,w\ge m-1\) | 一つの cut の \(r=2,3\)、\(4\le r\le8\)、\(r\ge9\) | \(2\le r\le e-1\)、\(\delta=0\)、relative top、\(w=m-1\) を含む |
| \(e=4,w\le m-2\) | \(u=3\)、\(u=4\)、\(u=5\)、\(6\le u\le8\)、\(u\ge9\) | 第一行は対応する小幅/三関係/幅4証明。第2–4行は一般高次評価と小幅基点 |
| \(e=5,w\le m-2\) | \(u=4\)、\(u=5\)、\(u=6,7\)、\(u\ge8\) | 最小幅・一欠落幅・小幅・大幅で全行。大幅の分類は第一行だけに必要 |
| \(e\ge6,w\le m-2\) | \(u=e-1\)、\(u=e\)、\(e+1\le u\le2e-3\)、\(u\ge2e-2\) | edge・one-hole・dense・sparse。全て \(u\ge e-1\) を満たし、隣接範囲の欠落なし |

幅は整数なので \(w\le m-2\) と \(w\ge m-1\) は排他的で全域を覆う。
狭幅正規化では \(q=e-2\)、\(u\ge q+1\)、\(d\ge1\)、\(m\ge du+2\) が従い、
\(m=du+2\) も含む。\(u\) と物理幅 \(du\) を等置しない。
full AP の \(d=1\) は source=target を保持する。

第0行は両側1。source の最小変数数 \(e\) を超える行は source が0。
\(i=e\) は各閉鎖証明の top として残し、\(i>e\) の自動処理に混ぜない。
target が source より早く消える場合に、正の source 上界を無条件に払わせる議論もしない。
特に一般容量法の \(u\ge i\) を外れる full AP 上端や N4 \(u=3,4\) は専用枝で処理する。

旧196組・83組・665比較・5tail はこの分割の節点ではない。
排除を正当化する代替は ordinary の actual Apéry–Sidon と scalar、N4 の全幅三関係計数と明示小幅/幅4証明である。
これは単なる coverage 表だけで代替証明の正しさを認定するという意味ではない。
本監査では全章の数学的再証明までは行わず、分割の論理と現在の形式化範囲、次節の共通章を独立に点検した。

## 4 共通章 `01_COMMON_JA.md` の数学レビュー

レビュー対象の改訂後 SHA256 は
`eb867a88f25165904e936b1fa642da5159883f5591ee48bcc23681b53ea51c77`。
章を直接編集せず、次の二つの軽微な指摘を親担当へ伝えた。
いずれも親担当が本文へ反映済みで、最終読解時には解消している。

1. \(m\ge2\Rightarrow e\ge2,w\ge1\Rightarrow v\ge1\) を明示し、\(\bmod v\) の正の法を保証する。
2. MINCAP の \(i=v\) の説明では、\(v=i=1\) のとき \(D<i\) 側が空である。唯一の \(D=1\) の直接代入を独立に一言残す。

以下の点に、残る数学的誤りは見つからなかった。

| 点検対象 | 独立に確認した理由 |
|---|---|
| 完備化と代数的接錐の同一基底 | 長さ \(n\) の原子積は有限個。各許容指数をその一つへ振り分ければ形式級数の \(\mathfrak m^n\) 表示を得る。正確 order \(n\) の指数は Apéry 表示 \(b+\ell m\)、\(\ell\le n\) で有限。積と原子作用が一致する |
| 同標数の体拡大 | 最小次数付き自由解消の flat base change は最小のまま。形式冪級数環全体の tensor 同型を仮定せず、有限な各級の単項式座標を介すればよい |
| 元 source の正規化 | 実生成元の値は \(m+da_j\) のまま。正規化 offset の gcd1、\(\gcd(m,d)=1\)、\(q+1\le u\)、\(m\ge du+2\) が元の数値半群と狭幅仮定から従う |
| completion の最小系 | 幅 \(<m-1\) では候補は全て \(<2m\)。幅 \(\ge m-1\) では \(m,\ldots,2m-1\) が全 \(n\ge m\) を帰納的に生成し、それ自身は分解不能 |
| CAP の剰余規約 | \(m=av+b\)、\(1\le b\le v\) と \(D=v-((m-1)\bmod v)=v-b+1\) は一致。\(i>v\) では該当二項係数が0になり、actual 容量は0 |
| MINCAP の範囲 | \(1\le i\le v\) でのみ最小容量式として用いる。\(D\ge i\) と \(D<i\) の正整数係数の最小が各1となり、端は別記された。\(v<i\) で0を越える下界を勝手に課さない |
| MINCAP の単調性 | 固定 \(i\) の二項係数は \(v\) に関して非減少、その最小と和も非減少。BRIDGE(d) は \(u\ge i\) の範囲で \(u\le du\) を適用 |
| ordinary 容量 | \(v=m-1,D=v\) により、\((v+1-i)\binom v{i-1}=i\binom vi\) と Pascal から \(i\binom m{i+1}\) を得る |
| LOWCAP の境界 | 第2行の \(v\ge3\)、第3行の \(v\ge5\) は正しい。第3行の二項係数最小候補を \(v=4\) へ延長しない |
| e=1 | 共通章の容量・正規化の仮定から除かれている。全域合成で \(S=\mathbb N\)、source=target を直接使う必要がある |

MINCAP の数式は Lean の `NSP14.Target.apLowerProfile` と同じである。
ただし既存 Lean は自然数引数への下界として全域定義し、紙上本文は最小容量の意味を明瞭にするため \(1\le i\le v\) を明記している。
一般定義の飽和減算と紙上の整数式の意味を混同しない。

## 5 公刊入力の照合範囲

共通章の版・定理番号・仮定は、V02 §1.2 と V03 の登録および現行実装の消費範囲に照合した。
本監査では下記原典全文を新たに取得して読んでいない。

| 入力 | 照合した登録 | 任意標数性と今回の適用上の注意 |
|---|---|---|
| Green | Caviglia §1 (1.1) 再掲、次数2 | 無限体上で使用、有限体は同標数拡大から戻す。原Greenと後続の標数制限付き強化を混同しない |
| BHP/EK | Juhnke-Kubitzke–Venturello §2.2 Lemmas2–3、Pardue の正標数版を含む | 同じ全 Hilbert 関数の一つの lex ideal。EK の ideal/quotient 添字差を保持。現行 Run18 の凍結型も任意 `Field k` |
| Kneser | DeVos Theorem1 | 有限群の定理なので係数体の標数に依存しない。合成数位数・非自明 stabilizer を含む |
| AP 公式 | Gimenez–Sengupta–Srinivasan arXiv:1108.3203 Theorem4.1 | 最小算術列生成系・任意体。非最小な区間全体を表示変数にしない |
| AP 接錐一致 | Herzog–Stamate arXiv:1308.4644v3 Proposition2.5 | AP source に限る一致を一般 source へ拡張しない |
| LTV | Lan–Tu–Vu arXiv:2307.05589v1 Theorem1.1 | 任意体の三生成元比較という登録を使用。理想/商の shift と literal completion の一致を保持。全幅 LTV の Lean export はこの SHA にない |
| SC | *Long zero-free sequences in finite cyclic groups* §4 Theorem8、math/0602568v1 | 群の列への unit 作用であって、元の数値半群・\(R,H_x\) 保存の主張ではない |

既存登録と実装の一致、保存レビューの存在、原典全文の独立再査読は別の確認である。
本稿は既知定理を通常の数学的引用として使うことができるが、引用したという理由だけで未実装 consumer を「Lean 完了」と数えない。
