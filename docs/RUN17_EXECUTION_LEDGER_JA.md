# Run17 execution ledger

指令: `docs/superpowers/plans/2026-11-13-run17-kneser-savchev-chen-order.md`
指令commit: `845b9c2ff3a047e62d53f639901452a030ca7981`。
採用work: `584f92d8c1a7fc1e2413f606b661fc9b81f472cd` (origin/work一致、着手時clean)。
Run16独立監査: `5ced6cc564e5c69bebcd7a852463091e2e276661`。
全11 ID PASS、指摘0、production修正要求なし。監査branchは独立に保持。
着手: 2026-11-13 JST。固定Lean/mathlibを変更しない。

## 実行上の判断

- ユーザー指定の既存workを継続。通常Pushまで許可済み。
- executing-plansをinlineで適用。cloud側実行helperはlocal実行ファイルでないため、
  既存Run16と同じくtracked ledger、凍結受入、実検証、一回の最終独立reviewを使う。
- 小補題・内部commitでrunを終了しない。X_KNESERとX_SCの一般命題を閉鎖条件とする。
- 原典取得用shellはSFU/arxivに対してproxy 403。利用可能なweb connectorで本文を取得。
  web抽出のhashはverification/run17/sourcesに保持。本文は実行scratchで照合。
  PDF原本のhashと偽らない。

## Pre-flight (着手時の状態)

| producer → consumer | 実契約 | 状態 |
|---|---|---|
| Kneser → iteration | 有限可換群、非空A/B、実stab(A+B)、thickening両辺 | 未実装 |
| iteration → cyclic | 商の非周期性、全n、合成数を含む | 未実装 |
| SC → words | Fin位置、全非空部分集合、単一unit、Nat代表総和 | 未実装 |
| Run16 → distance | shortestDegree : Fin u → Nat、全剰余で<u | 型確認中 |
| Run16 → QC | actual internalPoint、CoreMinimal、実QC単項式 | 型確認中 |
| additive → core | 同じD.u・正規化a_i、Wの定数1を保持 | 未実装 |

## 証明状態

X_KNESER / X_SCとTask1–5 consumerは実装・focused build完了。
全cold回帰・公理監査・一回の独立review・ZIP・通常Pushのgateは継続中。
現在の正式状態は`RUN17_CLOSURE_STATUS.json`を参照。基礎API・有限回帰だけを閉鎖と数えない。

## 履歴

1. 最新work、指令全文、Run16独立監査を確認。baseline `lake build NSP14` PASS (5894 jobs)。
2. DeVos Theorem 1全証明とSavchev–Chen v1 §§2–4を取得・読解。
   DeVosはportion最小stabilizerの帰納、SCは1-term・maximal extension・behaving subsequenceが本体。
   SC Proposition 2(a,b)は原典が先行文献を引用して証明省略するため、その部分もLeanで証明が必要。
3. Kneser既存形式化をMiscYD commit f2f1d413から発見。Apache著作権表示を保持し、
   固定依存上で両ソースの実証明がbuild PASS。一般有限群/実AddSubgroupへの接続kneserもPASS。
   Frozen KneserGoalと反復/成長/consumerは別途検証する。X_SCはOPEN。
4. SCの位置付きreindex・単射部分列・unit倍の保存、prefix和単射、一般有限群で長さ<card、
   全代表の正値性がbuild PASS。これらだけではSC完了にしない。
5. Kneserの商coset計数card_thickenがbuild PASS。
   SC補題の代替候補: sharpならS.erase 0⊆b+S。
   c∈Sから二回逆移動すると、b≠cの場合−b∈Sとなって零和自由性に反する。
   この一意性の代替証明を形式化中。
6. sharp_term_unique、反復同値項、極値subsetによるexists_sharp_terminal、
   sharp_terminal_unique、Connected導出木の構成がGREEN。
7. Connectedから実正係数・総和<addOrderOf・実subset sums=cyclic intervalを証明。
   long条件・位数の整除・ZMod gcdから生成元のunitを構成し、その逆で全位置を一括正規化。
   `savchevChen` / `savchevChen_positive` build PASS。
   原典Theorem8の一般型を弱めず実証明。Task3/5 consumerと最終検証は継続。
8. 実Aのcard=q+1、実coreのdegree/residueとnAの同値、最短距離との同値、
   全群生成、u−1以降の飽和がGREEN。
9. 実wordVolumeの定数1を保持した有限layer cake、正部分の成長和上界、
   q=2の1+u²/4、任意位置選択からの実端点因子(1≤K<選択長)、
   QC生存→ZeroSumFree→一般SCがGREEN。
10. SC具体列u6/u9、非unit項6、厳密半分境界u6[2,2,3]と全unit代表和7又は11がLean PASS。
11. 商のstabilizerでSet/Finsetの型輸送が過剰になる原因を調査。
    sumStabilizerの実体をSet actionへ統一し、Finset actionとの等式は既存定理で明示。
    数学的意味と凍結RequestedGoalsのbytesは保持し、quotientを跨ぐ不要なEq.recを避ける。
12. 任意商のstabilizer preimage、四点の実H=位数2、antipodalのNat表示とgcd、
    非antipodalの全n成長、三点のcollective gcd版がGREEN。
    実QCの二値混合語consumerも追加しbuild PASS。
13. Named具体受入 (群/列/実core/標数2QC) とroot build PASS (5964 jobs)。
    一般SCから(u−1)個のunit反復、List/Multisetの重複を保つ同値も証明。
    有限回帰PASS: Kneser 86,368対、反復4,554、零和自由multiset316うちlong92。
14. TDD履歴: 定義・Kneser・SC・距離のmissing export/module失敗をredへ保持。
    その他の構造補題の受入は実装中に型を具体化して追加した。未記録のREDを捏造しない。
    次は新規production/testを空cacheから全検証し、全生成宣言と過去契約を監査する。
15. Cold検証を開始。packagerはVERIFYING状態で期待どおり拒否し、ZIPを作らないことを確認。
    新規productionのlib/irとtest cacheを退避し、root buildがexit0。
    前runの全fixtureをimport依存順に再実行中。
16. 第1 cold試行は154受入と公理抽出がexit0。
    最後のbaseline照合が旧coordinate_model.jsonのseconds変更を検出してFAIL。
    旧checkerを直接実行したこちらの再生方法を修正し、原本をgit基準bytesへ復旧。
    変更結果と全試行ログはattempt_01_legacy_writeへ退避。
    正確な旧スクリプト/入力をtemporary rootで実行するwrapperを追加し、
    799座標とscheduleの同一結果・旧bytes不変をfocused検証した。
    singleton/prime/full Kneserの明示受入も補い、全cold検証を再度実行する。

Ruling: finishing-a-development-branchの統合先選択は、ユーザーが明示した既存workへの
通常Pushを適用する。改めて統合メニューを要求しない。検証・一回の独立reviewを省略しない。

## 完了条件

凍結RequestedGoals二命題の無条件実証明、反復/成長/actual consumer、全回帰、
公理・型・hash検査、原稿台帳、監査ZIP、一回の独立review、通常Push。
未証明の結論をstructure fieldやwrapper仮定へ移さない。

17. 最終cold検証 PASS_RUN17_PROOF_CLOSURE。159 commands、154 fixture、8,241宣言、
    新規406宣言の通常/explicit型、公理3種制限、source hash前後一致、
    全過去baseline bytes照合がPASS。正本はverification/run17/final/verification.json。
    proof snapshotをcommitして一回のfresh-context独立reviewへ渡す。

18. 初回fresh-context独立review: 数学的欠陥なし。全28 source/6 fixture、hash/public goal/actual consumerを確認。
    公開toolingにImportant 3件: 自runの証跡再利用、ZIP上書き、reviewとsnapshotの非束縛。
    Minor 1件: paper ledgerの予定表現。公開前に全件修正し同じreview seatへ再確認する。
    新規run出力をexclusive化し、数値JSONを同じrunへ揃え、既存archive/sidecarを拒否。
    実在Git commit、source/evidence manifest、全bundle静的fileをreviewへ束縛し、
    publication-onlyの明示境界だけを許す。数学sourceは変更しない。

19. 公開tooling修正版のcold検証 PASS_RUN17_PROOF_CLOSURE。160 commands、
    154 fixture、8,241宣言、新規406、450.127秒。Run01–16原本3,260件と
    既存Run17証跡368件のhash/bytesを保持。数学28ファイルはdc66f3aと完全同一。
    採用証跡: verification/run17/runs/release_candidate_20261113_r02。原本final/は変更していない。

20. committed candidate 7c38921のtemporary cloneで公開処理13ケースPASS。
    正のZIP生成、再実行による上書き拒否、checksum単独の既存先拒否、
    全ゼロcommit/実在する古いcommit/誤ったsource又はevidence manifestの拒否、
    未review文書変更の拒否、明示したledger追記境界の成功を実測。
    synthetic reviewはtemporary clone内のtool testのみ。実作業treeのreview gateはpendingのまま。
    証跡はpublication_tool_checks.json。これを固定して同じreviewerへ再確認を依頼する。

21. 同じfresh-context reviewerが8577773を再確認しReady。Critical/Important/Minor=0。
    13ケースを独立再実行し、707 source/168 evidence、旧Run17証跡368、過去3,260を照合。
    source/evidence manifest hashはfinal_review.jsonの実値へ束縛。
    Declined scopeの裁定: 実ZIPの全entry/hash/CRCと通常Push/remote cleanは実行側が続けて検証。
    readonly reviewでの全cold再実行は対象外とし、記録済み160コマンドと独立focused検証を採用。
    Run18–20の数学と全P14完成は今回の承認範囲外。

22. 実監査ZIPを生成。598格納file+2管理entry、1,456,429 bytes。
    全entry集合・全SHA・CRCをpackagerと別読み込みで照合しPASS。
    実packagerを再実行して既存ZIP拒否とhash不変も確認。
    archive SHAは隣の.zip.sha256。通常Pushとremote/clean照合へ進む。

23. release b85438dd46bfdd920c7b6117c5541b2078094b09を通常Push。
    fetch後origin/workとrelease SHAが一致し、worktree cleanを実測。
    この公開確認をmetadata receipt commitへ追記し、再度通常Pushする。
