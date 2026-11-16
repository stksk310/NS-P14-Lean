# GitHub・Zenodo公開準備

2026-11-16 JST。今回は公開準備のみ。公開版番号・公開日・DOIは未確定。
著者はKeisuke Sato、ORCIDは[0009-0005-4230-0268](https://orcid.org/0009-0005-4230-0268)。
コードApache-2.0、論文・説明文CC-BY-4.0は著者が本作業で指定した。

## 現在地

調査基準は`work`のcommit `342fbdda072fc5d6aa5e8f2d8968456cc54c12a6`。
GitHubのvisibilityはprivate、default branchはmain。
`main`は初期化commit `1b55ecb3c3ca6af975fdd6747d9f7e4d2bb86644`のままであり、
実装・証跡は`work`にある。公開前に入口のブランチを整える必要がある。
この準備ではdefault branch・visibility・既存workを変更しない。

[Run19完了receipt](../../verification/run19/RUN19_COMPLETE_20261116_R03.json)は
`RUN19_COMPLETE`、`all_P14_complete: false`を記録する。
[その後の独立監査push receipt](../../verification/run19/publication/independent_audit_push_20261116_r01.json)も
全P14未完を明記する。Run20の`I_PARTITION`・`I_MAIN`と最終全域合成が残る。
これらは保存された過去の検証結果であり、今回の新規Lean検証ではない。
`docs/RUN19_CLOSURE_STATUS.json`などsource凍結時の途中状態を、完了receiptと混同しない。

V06原稿も過去の固定SHAを対象にした文書である。原稿の「未実装」一覧だけで
現在のLean到達範囲を判断せず、Run19のreceipt・対応台帳と合わせて読む。
古いREADME節、AUDIT_HANDOFF、原稿、レビュー、ZIPはその時点の履歴資料として保存する。

## 今回用意したもの

| ファイル | 用途 |
|---|---|
| [README](../../README.md) | 最新状態、読者の入口、固定環境、再現手順 |
| [CITATION.cff](../../CITATION.cff) | GitHubの引用情報。著者・ORCID・softwareの位置付け |
| [.zenodo.json](../../.zenodo.json) | 将来のGitHub連携向けメタデータ。Zenodo APIのdeposit要求bodyではない |
| [LICENSE](../../LICENSE)・[適用範囲](../../LICENSE_SCOPE.md)・[CC本文](../../LICENSES/CC-BY-4.0.txt) | 著者が指定した二つのライセンスと対象の区別 |
| [NOTICE](../../NOTICE) | Kneser由来コードの既存著作権・出典の案内 |
| [release notes draft](RELEASE_NOTES_DRAFT.md) | 公開対象の状態を確定してから使うリリース説明 |

DOI、公開日、版番号は推測で埋めない。CFFの`version`・`date-released`は
公開版を決めてから追加する。`.zenodo.json`は将来の連携でタグ等から得る版情報を
妨げないよう、未確定のversion・publication_date・doiを指定していない。
二つのファイルの著者・タイトル・license・未完の説明は揃える。
ZenodoのGitHub連携では`.zenodo.json`がCFFより優先される実装があるため、
CFFだけを更新して登録情報も更新されたと考えない。

## 公開時の手順（まだ実行しない）

1. **公開範囲を決める。** Lean化完成後の公開か、未完成の開発snapshotかを決め、
   対象commit・版番号・タグを固定する。現時点で全P14完成とは記載しない。
2. **GitHubの入口を決める。** `work`の成果をmainへレビューして統合するか、
   default branchをworkへ変えるかを決める。初期mainを誤ってリリースしない。
   準備ブランチの文書・ライセンスも公開対象commitへ含める。
3. **内容と権利を確認する。** 全公開ブランチ・タグ・Git履歴、47個の既存ZIP、
   PDF・ログ・添付資料を対象に、秘密情報・公開しない個人情報・第三者資料を確認する。
   Git commitの氏名・メールも公開される。`.gitignore`は既に追跡されたファイルや
   過去の履歴を非公開にする機能ではない。履歴改変・古い証跡の削除は別途判断する。
4. **再現性を確定する。** 対象commitに応じたfresh検証・型・公理依存・全域被覆の記録を取り、
   最終レビューと照合する。旧receiptを新しいcommitの検証結果として流用しない。
   Run19検証器は旧README等も凍結照合するため、新規公開文書を追加したこのツリーへの
   適用は想定しない。旧結果の再現にはREADMEの固定commit・別checkout手順を使う。
   公開commit自体の認証方法は、その版の変更範囲を明示して別途整備する。
   Run20が入るなら、その検証入口と全P14の証拠をREADMEへ反映する。
5. **引用情報とライセンスを確認する。** 著者・ORCID・二つのlicense scopeを確認し、
   CFFに版番号・公開日を追加する。論文を別Zenodo recordにする場合は、softwareと
   別のタイトル・resource type・CC-BY-4.0で登録し、相互リンクを付ける。
6. **GitHubを公開し、Zenodoを設定する。** 公開実行の指示を受けてからvisibilityを変える。
   GitHub連携を使う場合、Zenodoで対象repoを選び、公開対象のリリースをアーカイブする設定を確認する。
   連携後のGitHub Release公開はZenodoへの公開・DOI発行につながる操作として扱う。
   下書きReleaseやタグだけで、Zenodo登録完了とみなさない。
7. **配布物を固定して公開する。** 連携のGitHubタグsnapshotと手動uploadの二重登録を避ける。
   任意のRelease添付ZIPがすべて自動収録されると仮定せず、Zenodo上の実ファイル一覧・サイズ・
   hash・ライセンス文の同梱を確認する。特定ZIPが必要なら配布方法を先に決める。
8. **DOIを実測で反映する。** 登録された版DOIをその版の引用に、concept DOIをプロジェクトの
   継続リンクに使う。実際の登録結果を確認してREADME・CFFへ追加し、GitHubのタグ・commitと
   Zenodoの配布物が対応することを記録する。元リリースへ後からcommitを追加した扱いにしない。

## 配布量と今回の確認範囲

基準commitのtracked treeは11,086ファイル、422,329,566 bytes（展開時）、ZIP 47個。
最大の通常ファイルは約59 MBで、検証の宣言一覧・公理ログが容量の多くを占める。
これはGit packやZenodo uploadの圧縮サイズとは異なる。巨大ログを除く場合も、
監査用manifestとの整合性を検証した別の配布物として扱い、元の監査ZIPを上書きしない。

今回のファイル名確認では典型的な`.env`・秘密鍵・credentials名は見つからなかった。
これは内容・過去の全履歴・全ブランチ・ZIP内の秘密情報検査を済ませたという意味ではない。
公開前の内容確認は未実施の項目として残す。

Leanコード・固定依存・過去の検証器・原稿・証跡は変更対象にしない。
今回の検証は新規公開資料、メタデータ、参照先、および既存ファイルの不変性を対象とする。
新しいLean build、Run20、全域の公理監査、Zenodoアカウント内のdraft/record照会は実施しない。
ここでDOI未確定とするのは今回用意した公開版についてであり、既存recordの不存在確認ではない。

## 参照

- [Zenodo公式GitHub連携案内](https://help.zenodo.org/docs/github/)
- [GitHub公式の引用情報案内](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
- [Zenodo連携のメタデータ選択実装](https://github.com/zenodo/zenodo/blob/master/zenodo/modules/github/api.py)
- [CFF仕様](https://github.com/citation-file-format/citation-file-format)
- [CC-BY-4.0本文の取得元](https://github.com/spdx/license-list-data/blob/main/text/CC-BY-4.0.txt)

公式ヘルプ本文の直接取得はこの環境のproxy 403で不可だったため、上記のヘルプUIの
現行挙動を実操作したとは主張しない。公開時には最新のZenodo画面・案内で手順を確認する。
メタデータの優先関係は取得できた公開実装を参考にしており、稼働版との一致の認定ではない。
