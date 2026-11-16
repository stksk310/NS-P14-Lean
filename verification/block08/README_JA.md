# Block08：実半群・Apéry・原子・order・数値headの基盤

2026年11月10日（JST）。6ファイル・85定理と、証明付きのterminal/head全単射をまとめた作業単位。
Block01–07のソース・テスト・固定依存revisionは保持する。

## 完成したもの

| ファイル | 構成と結論 |
|---|---|
| `Semigroup/Basic.lean` | 実際のcofinite AddSubmonoid ℕ。最小正元multiplicityと各剰余の元の存在 |
| `Semigroup/Apery.lean` | 各剰余の最小元、濃度m、一意分解x=ω+qm、predecessor不在の特徴付け |
| `Semigroup/Atoms.lean` | 有限なactual原子集合、その生成性と最小性、actual埋込次元0<e≤m |
| `Semigroup/Order.lean` | 最長分解の存在・有限上界・超加法性、原子表示長との一致 |
| `Semigroup/AperyGrading.lean` | 次数0/1/≥2の濃度、二次層≤δ、全Apéry元order≤δ+1 |
| `Semigroup/Heads.lean` | terminal/non-Apéry headの数値全単射、jump≥2、head次数≥3、live条件とjumpの向き |

`NumericalSemigroup` の入力は実際の加法部分モノイドと、あるconductor以降がすべて所属する証明。
conductorの最小性は要求しない。multiplicityや原子や最小代表の存在を未証明のフィールドとして渡していない。

## Apéryと最小生成系

各剰余の元はconductorの倍数に剰余を加えて実際に作り、Nat.findでその最小元を取る。
この最小性はBlock02と同じ `IsAperyMin S.carrier S.multiplicity` に接続する。
代表は剰余から復元できるため単射で、Apéry集合の濃度はm。
すべてのx∈Sはω+qmと一意に分解され、自然数減算はω≤xやpredecessorの存在で正当化する。

原子は正のindecomposable元。m自身は原子で、その他の原子はApéryに含まれる。
従って原子集合は有限である。正元を分解する強帰納で原子がSを生成することを証明し、
生成集合のclosure inductionで、どの生成集合も原子を含むことを証明する。
埋込次元eはこのactual原子集合の濃度として定義する。

## orderは原稿と同じ量

`HasLength x n` は正の実半群元n個への分解。各元はm以上なのでnm≤x、特にn≤x。
これにより最大値 `order x` と、その最大値を実現する分解が存在する。
最長分解の各因子は原子であることを `longest_factors_atoms` で証明した。
逆に任意の原子表示の長さはorder以下なので、原稿の最長生成元表示長と一致する。
単に「正元表示」と「原子表示」を同じものとして仮定していない。

order0=0、orderm=1、order1と原子の同値、超加法性を証明する。
Apéryの次数0は{0}、次数1はm以外の原子。
残りの次数≥2の集合の濃度はδ=m−eであり、二次層の濃度もδ以下。
最長Apéry表示から一原子ずつ外すと、Apéry性を保って次数が1ずつ下がる。
各次数の代表をhigh集合に単射にし、全Apéry元のorder≤δ+1を得る。

これらは数値集合の濃度である。actual商Qのfinrankと同一化する代数の証明はまだ含まない。

## terminal/headの正確な範囲

terminalはord(x+m)>ord(x)+1。非Apéry x-headは、Apéry外でliveなincoming m-arrowがない数値ラベル。
`terminalHeadEquiv` はx↦x+m、逆y↦y−mを証明付き全単射として構成する。
逆の自然数減算は、headに実際のpredecessorが存在することから正当化する。
terminalは正、jump≥2、対応するhead次数≥3。

liveなbase作用ではjump非減少、liveなhead作用では非増加。
同jumpの場合にだけlive条件が一致することを証明する。
**globalなT≅Nの加群同型は主張しない。** 今回は数値ラベルとorderの等式であり、
実際の環・加群の作用との同定は後続工程。

## 具体例と回帰

- ℕ全体：conductor=0、m=e=1、order x=x、δ=0、terminalなし。
- Γ=⟨3,4⟩：conductorの証拠6、m=3、Apéry={0,4,8}、原子={3,4}、e=2、δ=1、order8=2。
  actual m/eを持つ数値Apéry-pairデータをBlock02へ渡し、multiplicity下界が成立することも確認する。
- Γ=⟨6,7,15⟩：conductorの証拠30、m=6、15は原子でorder15=1、order21=3。
  15がterminal、21が非Apéry head、jump=2、全単射の値が21となる。

これらは定理の仮定を架空のprofileで満たした例ではなく、明示した実半群から導いた数値である。
一般定理は有限例から外挿せず、上記の普遍証明で得る。

```sh
python3 scripts/verify_block08.py
```

このクラウドでは先頭に `PATH=/tmp/ns-p14-lean/bin:$PATH` を付ける。
build、6ソース再検査、新テスト、既存7Block回帰、既存2監査を実行する。
新規85定理に加え、証明を含む `terminalHeadEquiv` 定義の公理依存も検査する。
新規86報告＋既存106報告、計192件。標準3公理以外を拒否し、完全名と既存19ファイルのhashも照合する。
過去の検証ログ・manifest・ZIPは保持し、今回の照合対象はこのディレクトリのmanifestとする。

## 未完の接続

数値座標基盤は実半群から構成済み。
actual completed-semigroup tangent coneとの環同値、A/T/N/Qの基底への同定、
同jump stratumの加群同型、jump上限、least-offset経路・volume・cut・tower、
最大actual Q₂からのpairデータ、Tor/BettiとP14全体は後続工程。
原稿との定義対応と証明の位置付けは [対応台帳A10–A11](../../docs/LEAN_PAPER_ALIGNMENT_JA.md) に保存する。
