# Run15 — 証明済みexportと未完宣言

**判定：PARTIAL_NOT_RUN15_COMPLETE。ordinary主定理は未証明。**

数学ソース基準は `fbfa5debe3daa115b610ecc72dedc8fd52a817ca`。
途中でorigin/workへ公開された再現性修正 `20aadbf7011692eb3bfffef49029e2c5e416ef3d` をfast-forward統合した。
同修正は数学ソースを変更せず、Run14再実行の絶対出力先を現在のcheckoutへ修正する。
指定指令はcommit `586019b1c3063ac7160b1fc83a7da66ebbcf7311` の全文を保持している。

## 閉じた接続

| 証明済みexport | 実際に保証する範囲 |
|---|---|
| `ActualWitness.relativeToG`, `relativeG_finite` | R=L[Option(Fin r)]、noneがactual x、someが同じcut。有限headをxで生成する実証明。GのP有限性・k有限性は追加していない |
| `basisExtendingPrefix`, `extendedPolynomialEquiv_prefix` | 非x一次空間の基底拡張と実多項式代数同値。選んだ各λをliteral polynomialとして保持。補変数数f=e−r−1 |
| `toPolynomialRing_injective`, `polynomialRetraction_comp`, `relativeToFull_injective` | P→S₀とR→全e変数環のsplit単射。A/G内の像の代数的独立性ではない |
| `cutA_finite`, `cutT_finite`, `cutHigh_finite`, `cutK_finite` とcoefficientFinite群 | 同じP作用での有限生成、A/T/X/M/Kの係数体上有限性。Gは係数有限群へ含めない |
| `bettiEuler_shortExact`, `bettiEuler_kernel`, `koszulCorrectionRank_le` | 実LESのconnecting rankとその補数を区別した整数Euler恒等式。H₀を保持 |
| `finite_koszul_bettiEuler`, `finite_koszul_bettiEuler_top` | 有限k次元加群の実Koszul境界rankによるEuler公式とcᵣᴾ=0。無限k次元chainへのfinrank加法を使わない |
| `cutTower_kernel_le` | 実短完全列0→Kₛ→Mₛ→Xₛ₊₁→0から第3Tor不等式。δの消滅を仮定しない |
| `descendingStratumEuler_eq`, `cutTEuler_le_sum` | 同jumpの実P同型と反対向きのjump filtrationから第2Tor不等式。global T≅Nは使わない |
| `ArithmeticSequence.Data.source`, `embeddingDimension` | 任意d≥1、gcd(m,d)=1、1≤v<mのactual AP半群、cofinite、真正な最小原子v+1個 |
| `canonical_order`, `aperyValue_min`, `xMultiply_injective` | 一般APの標準指数表示、全actual Apéry元、order(x+m)=order(x)+1、actual接錐上の全線型結合に対するx正則性 |
| `fullPolynomialToSemigroupRing_surjective` | actual最小原子による代数的半群環の全e変数表示と有限生成。接錐との同型は主張しない |
| `intervalCompletion_carrier`, `intervalCompletion_embeddingDimension`, `intervalCompletion_ordinary_mem` | 最大actual原子からliteral interval closureを構成。最小原子数min(w,m−1)+1、wide時にcarrier={0}∪[m,∞) |
| `ordinary_target_difference`, `ordinary_h0_correction` | 既存のTargetMargin.targetそのものへの正確な係数畳み込みとH₀補正係数。actual Bettiの定理ではない |

## 正確な未完の型

`audit/run15/RemainingGoals.lean` は次の命題を **def : Prop** として固定する。
証明・axiom・未証明structure fieldは与えていない。productionはこの監査moduleをimportしない。
コンパイル成功は命題の型が定義できることだけを意味する。

1. `APBettiGoal`：GSSの一般AP quotient Betti公式を、actual代数的半群環の通常Torから導く。
2. `APConeBettiGoal`：同じactual最小表示による半群環と接錐のBetti一致。原点の半群環と接錐の代数同型は不要。
3. `HarmonicGoal`：任意q生成元の同shift有限長P加群について、実kernelの初期加群・実Koszul行列rank・任意標数の±1 minor計数を経てharmonic上界を証明する。
4. `RelativeTerminalGoal`：GのR上のcᵣ₊₁ᴿ=0。証明済みの有限長P層のcᵣᴾ=0はこれを代用しない。
5. `ActualTorToRowGoal`：x-KoszulのA/T比較、B=A/X₂の実P加群同定、第2/3鎖とharmonicの同H適用を合わせ、実cⱼᴿ(G)を既存rowへ接続する。
6. `CorrectedFullTransferGoal`：actual H₀の同じZ作用を含めた有界比較。高次R-Bettiの和をj=1から始め、第0補正f+1を保持する。
7. `OrdinaryBettiBoundGoal`：wideな全source、任意体、全正Betti行のactual bound。cut/harmonic/比較結論を引数にしない。
8. `OrdinaryActualCompletionGoal`：元の任意体上、sourceとactual interval targetそれぞれの最小全変数表示、literal完成接錐、0行を含む全行。

これらに加え、一般線型変数変更による通常Tor保存、P制限した層のgradingとの接続、
一般APのD端点・Fmin単調性・actual target Betti同定も、対応する上位接続の内部作業として残る。

## 解けていない障害の内容

初期加群について、既存`standardMonomialBasis`はscalar idealの商に対する定理である。
任意の実表示P^q→Zのkernelへ適用できるmodule版、商基底の次数保存、
その基底での実Koszul境界の三角化を今回構成できていない。
既存`triangular_signed_minor_rank_lower_bound`は**選んだ実minorが三角であること**を前提とするので、
それだけではharmonic計数の必要なminor存在を供給しない。
有限Euler公式だけからharmonicや非負性を推論することもしていない。

一般APについては、canonical orderとx正則性を示したが、GSSのminimal resolutionの
exactness・minimality・rank、又は等価な実Koszul計算を構成できていない。
x正則性だけからrank公式は出ない。半群環の表示を新たに実装したため、
未完のBetti比較自体は実対象の型で固定できた。

相対GのR有限性とR→全表示の単射性も、それ自体では変数変更のTor保存や
H₀のZ作用を保った二重複体比較を与えない。ここは未証明のまま明記した。
以上は形式化の未接続であり、原稿の数学的反例を見つけたという意味ではない。

## 原典との対応

原典PDFはweb connectorで閲覧し、任意体・quotient/ideal添字と仮定を確認した。
最初の直接curlはhost policyでCONNECT403だったが、閲覧可能な別ツールで解決した。

- Gimenez–Sengupta–Srinivasan, https://arxiv.org/pdf/1108.3203 ：Theorem3.10の解消構成とTheorem4.1のquotient Betti公式。m=av+b、1≤b≤v。今回その解消は未形式化。
- Herzog–Stamate, https://arxiv.org/pdf/1308.4644 ：Proposition2.5のAP ideal/cone Betti一致。最小生成のAP、標準基底と最小原子変数の正則性を用いる。今回x正則性をactual coneで証明したが、一致全体は未形式化。

原典を読んだ事実、機械検算、Leanの実証明を区別する。
