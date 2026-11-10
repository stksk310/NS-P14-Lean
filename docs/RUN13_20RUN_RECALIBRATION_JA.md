# Run13実測による20run計画の再校正

2026年11月10日JST。旧R02 schedule/checkerは履歴として保持する。
途中版の24〜28runという見積りは、今回同じRun13内で閉じた複数境界を追加runへ分割した仮見積りだった。
ユーザーの「小ファイルでは終わらず、数学的接続が閉じるまで同じrun」という単位に合わせて再計測する。

Run13は途中版23ファイル・1,852行から、継続後には69 coreファイル・5,895行の共通基盤へ拡大した。
正確なファイル・宣言・生成宣言・検査時間は`verification/block13_continuation/verification.json`を正とする。
キャッシュ使用の検査時間を、研究・実装・初回mathlib依存ビルドの所要時間とは読み替えない。

## 目標配分

| run | 閉じる接続 | 主な不確実性 |
|---|---|---|
| 14 | 実cut・正則性・offset/有限商・同標数拡大の実適用 | actual regular sequence/安定化の証明量 |
| 15 | ordinary/AP target・harmonic・初項rank | 全競合の初項証明、組合せとactual商の接続 |
| 16 | ordinary Tor/tower・補正rank・端点への入力 | 実filtration/connecting mapの同定 |
| 17 | 共通端点のactual移行・五生成元以上の幅側 | kernel・Tor補償・全分岐の接続 |
| 18 | BHP/Pardue/EK等の必要な公刊入力 | 固定mathlibにない比較定理の新規証明量 |
| 19 | N4/LTV/三生成元・小ordinary残余 | 公刊入力と算術部分の閉鎖 |
| 20 | 統合・全actual回帰・最終仮定/公理監査・原稿照合 | 未供給依存の発見、最終対象の量化 |

全体20runは再び目標配分として保持できる。ただし達成保証ではない。
とくにRun18/19は公刊入力の証明量を入口で再測定する必要があり、現在の根拠だけで20run以内を認証しない。
必要なら1runをさらに長くし、完成条件や独立した数学の入力を弱めて数を合わせることはしない。

## 今回からの修正

- 極小自由解消rankは、未実装の汎用Tor/Tor' balancingを新規に作る代わりに、実syzygy短完全列のKoszul LESで閉じた。
- gradingはactual座標・既存次数に基づくwitnessから実dを制限し、chainのk有限性に依存しない。
- 体拡大は実L[X]作用とactual指数行列から供給し、形式級数環全体のtensor同型を不要にした。
- 検証はソース正規表現の宣言一覧から、Lean環境が持つ生成宣言・構造射影まで含めた公理依存一覧へ拡張した。固定Lean4のproof-erasure stubは依存情報で真正公理と区別する。
