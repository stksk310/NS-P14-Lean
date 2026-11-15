# 短縮後の依存と全域被覆

読解基準は work `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
下図の矢印は入力から結論へ向く。公刊入力の一般的再証明は含めない。

```mermaid
flowchart TD
  B["BRIDGE：元source・完備化・物理幅・actual容量・境界"] --> M["MAIN：任意体・全Betti行・各自の最小表示"]
  SM["e≤3：直接計算／LTV"] --> M
  OC["ordinary：数値Apéry・同jump・一つのcut／塔"] --> OH["harmonic rank／Tor三段／H0補正"]
  OH --> OS["全行scalar／一つの固定cutoff恒等式"]
  OS --> OL["r=2,3：直接"]
  OS --> OM["r=4..8：actual Sidon＋五行"]
  OS --> OU["r≥9：障壁／連続floor比較"]
  OL --> O["ordinary全域"]
  OM --> O
  OU --> O
  O --> M
  EC["整数core／有限内部語／全長競合／実核"] --> ER["T角の上界／元のPC,W,Hx,R"]
  EC --> ET["QC→QG実核長のTor補償／端点Euler"]
  ER --> ET
  ET --> EG["一般qの共通行評価"]
  ET --> E2["q=2の四行"]
  EG --> WE["e≥5：full AP／一欠落minor"]
  EG --> WD["dense：一つのlex／K／容量差"]
  EG --> WS["sparse：第一行資源／第二行→全高次"]
  EG --> WF["e=5：u6/7／全高次／第一行分類"]
  AP["APD：候補語spanning＋整数容量+1"] --> WF
  ER --> AP
  EG --> AP
  WE --> W["e≥5狭幅全域"]
  WD --> W
  WS --> W
  WF --> W
  W --> M
  E2 --> NN["N4：三点距離／SC復帰／socle三角形"]
  NN --> NH["高次行：一つの三次式"]
  NN --> NF["第一行：三関係計数／幅6–8"]
  EC --> N4["幅4：全競合／L′,K′／実像独立"]
  NH --> N["四生成元狭幅全域"]
  NF --> N
  N4 --> N
  N --> M
```

APD.2 は一般距離和・E-ARTIN・実核補償E-TORを使う。APD.3 は幅章の全高次行を再確認する
適用説明であり、APD.2の前提ではない。W-FIVE-FIRST→APD.2→W-FIVE-FIRSTという循環はない。
同様にE-TORはE-STOPの明示的停止値を使わず、有限内部語によるE有限性を使う。
E-STOP自体は本文に証明を残した。

## A・B・Cの分類

| 分類 | 内容 | 扱い |
|---|---|---|
| A：必要な核心 | ordinary同jump strata／同じcutの資源／rankとTor／actual Sidon、端点の全競合・実核補償、denseのwhole-Hilbert lex、N4のSC復帰・三角形・幅4 | 証明を本文化して保持 |
| B：共通接続 | 完備化、同標数体拡大、元sourceの正規化記述、物理幅、actual target、0行・上方行 | BRIDGEへ共通化 |
| B：同型の算術 | 小／大ordinaryの二変数差分、denseの容量差、sparse第二行 | 一つの恒等式または差に統合 |
| C：不要な強化 | exact antipodal presentation・P/W/b1、N角からのR厳密算出、ordinary余剰Γ全式、N4四次・五次支払い | 数学的依存から除去。必須付録にもしない |
| C：既に外れていた別経路 | 196組、83組・665比較・5tail、Navi増分 | 再導入しない。今回新たに削減した量には算入しない |

## パラメータとBetti行の被覆

| 領域 | 全ての分割 | 有効条件 | 行 |
|---|---|---|---|
| 小生成元 | e=1／2／3 | e1は空gcdを定義しない。e3はLTV | 全i≥0 |
| ordinary | w≥m−1、r=2,3／4..8／≥9 | r≤e−1。r≥3はδ≥a_r。r≥9はe≥10。r6..8の角はactual Sidonで除外 | 1≤i≤eを証明、0行とi>eはBRIDGE |
| e≥6狭幅 | u=e−1／e／e+1..2e−3／≥2e−2 | q=e−2、d≥1、m≥du+2、collective gcd条件 | 同上、i=eも保持 |
| e=5狭幅 | u=4／5／6,7／≥8 | u≥8の全高次行は構造によらない。第一行だけantipodal分類 | 同上 |
| e=4狭幅・第一行 | u=3,4／5／6,7,8／≥9 | 幅4最後の族はm=6／m>6の全四剰余 | i=1 |
| e=4狭幅・高次 | u=3／4／5／≥6 | u≥6だけ新cubic。小幅の床とactual容量を保持 | i=2,3,4 |

- w=m−1はordinary側。狭幅ではu≤du≤m−2、最小境界m=du+2を含む。
- full APのd=1はsource=targetを使う。一般Fmin(u)による無理な支払いをしない。
- i=eを「source消滅」としない。i>eで初めてHilbert syzygyを使う。
- i>eでtargetが生きる場合も許す。u=4のtarget第4行最小値は1、source上界0と区別する。
- MINCAPの単調性は固定iに対してv≥iの範囲で使う。v<iにはactualの0行を適用する。
- 偶奇、床、負二項添字、max(Hx−2,0)、実核長PC−PGは本文で定義域を明示する。

## 除外した結果の再流入点検

| 除外対象 | 他枝での必要性 |
|---|---|
| exact antipodal四モジュール | Width.Closureの再帰importからAntipodalBasis/Presentation/Ideal/Volumeへ到達しない。宣言名の他production参照も比較ルートにない |
| exact N_s全角 | 幅担当・N4担当が、実Rの定義とR≤Rhatだけを使用すると確認。幅4は独自の全競合を直接処理 |
| ordinary Γ_j全式 | targetへの十分な下界だけを使用。O6以降にΓ_jなし |
| old四次・五次N4比較 | N4b–cと小幅表が全高次行を閉じる。他枝は使用しない |
| 旧列挙証書 | 本文の数学的前提、DAG、数値入力に含めない |

既存Leanの集約importが独立成果を公開することは、紙上主証明の数学的依存とは区別する。
今回行ったのは読解・静的照合・新稿の独立レビューであり、新しいLean全域認証ではない。
