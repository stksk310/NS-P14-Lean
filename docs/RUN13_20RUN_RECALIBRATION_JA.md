# Run13実測による20run計画の再校正

2026年11月10日JST。旧R02計画と50項目checkerは履歴として保持する。
Run01–12は既存の閉鎖単位、Run13は今回の証明済みexportを持つ**未完のrun**。

## 観測

- mathlibにはTor/projective resolution/一般homology完全列があるが、固定版にはKoszul複体がない。
- 実微分、正次数exactness、augmentation、有限自由解消、通常Tor比較、全変数annihilation、k有限性まで独自の接続が必要だった。
- 基本部分だけで23新規coreファイル・約1,850行（最終正確値は検証JSON）になった。
- さらにgraded構成・resolution balancing・actual polynomial base change・有界filtrationの独立した境界が残った。
- 行数やビルド時間から公刊7入力の所要時間を予測できるとは扱わない。今回の実測は「共通基盤を1runで全部閉じる」R02の配分が過小だったという証拠である。

## 配分の修正

1. **Run13を継続**：Tor比較の自然性、Koszul短完全列、数値受入例、極小解消rank/balancing。
2. **同じ共通基盤の残り**：graded Koszul/homology、有限台とtotal和、同jumpのshift s。
3. **体拡大の閉鎖**：実L[X]加群・自然な複体同型・actual G/T/A/N/Q・I_FIELD。
4. Run14のcutへ進む前に、上の必要exportが閉じたかを判定する。未完のX_BASIC/I_FIELDをinputにしない。
5. 元Run15（AP target/harmonic/Tor鎖）、Run18（BHP/Pardue/EK）、Run19（N4/LTV/三生成元）も複数の大きい理論を束ねている。各々の入口で公刊入力の証明量を再測定する。

20runは引き続き希望目標だが、現時点で達成できると認証する根拠はない。
上の共通基盤を少なくとも2〜3個の追加閉鎖単位として見込み、公刊入力の不確実性も含めた
**暫定レンジを全体24〜28run**へ修正する。これは実行保証でも、定理の完成条件を弱める変更でもない。
Run13継続でbalancing/graded/base-changeが想定以上にまとまれば再圧縮できる。

## 再測定の基準

ユーザー操作や小ファイル数をrun数に換算しない。
証明済みの実比較・前提の供給・actual受入検査が閉じたまとまりを完了単位とする。
今回Run13を「Task1–8完成」とカウントして残り7runへ進むことはしない。

最終検証実測：core23ファイル・1,852行・183宣言（88 theorem）、fixture46宣言。
55コマンドの合計126.860秒（キャッシュ使用、研究/実装/初回依存ビルドの時間ではない）。
970公理依存レポートと旧84 hashの照合を含む。
