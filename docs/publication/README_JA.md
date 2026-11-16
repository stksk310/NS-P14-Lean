# GitHub・Zenodo v1.0.0 公開

2026-11-16 JST。著者Keisuke Sato、ORCID [0009-0005-4230-0268](https://orcid.org/0009-0005-4230-0268)。
コードApache-2.0、原稿・説明文CC-BY-4.0。

## 公開対象と根拠

ユーザーはGitHub Releaseの公開と、既存Zenodo連携による保存・DOI発行を明示的に指示した。
さらに、監査済みLeanコードと現在リポジトリ内にある資料を先に公開すると指定した。
別チャットに保存された最新英語論文ZIPは今回の版には含めない。
日本語の歴史的原稿とその古い到達範囲の表示は、元のbytesを維持して収録する。

[Run20完了receipt](../../verification/run20/RUN20_COMPLETE_20261116_R03.json)と
[最終独立監査](../../verification/run20/independent_audit_20261116_r01/AUDIT_JA.md)が全P14の完了を記録する。
監査後の基準commitは`e72713965716d7f93f672034c6332a79b59b1c53`。
公開文書追加後のコードがその基準から変わっていないことを、Git blob単位で照合する。
旧READMEは公開説明の更新対象として例外を明示する。Leanの新規実行は今回の作業に含めない。

## 配布資料

- [公開版説明](RELEASE_NOTES_v1.0.0.md)
- [固定manifest](RELEASE_MANIFEST_v1.0.0.json)：コード基準commit、元の監査ZIPと8件の証跡のSHA-256
- [CITATION.cff](../../CITATION.cff)・[.zenodo.json](../../.zenodo.json)：著者・ORCID・版番号・ライセンス
- [ライセンス適用範囲](../../LICENSE_SCOPE.md)・[NOTICE](../../NOTICE)
- [元のRun20監査ZIP](../../artifacts/NS_P14_LEAN_RUN20_COMPLETE_20261116_R03.zip)

根拠の正本は過去の固定proof/evidence/audit receiptである。
公開用資料のチェックを、Leanの再検証や数学の新しい独立監査とは呼ばない。
固定Lean環境と過去のverifierを再実行する手順は、ルートREADMEの別checkout手順を使う。

## 公開処理

`.github/workflows/release.yml`はv1.0.0タグのpush時に動く。チェックアウト対象を同タグに固定し、
GitHubが発行する当該jobのrepository tokenを使う。外部サービスのtokenや新規depositは作らない。

1. [公開用テスト](test_publish_release.py)で、変更された証明bytes、不一致のasset、別repo/版/著者のrecord、欠損・改変されたZIPを拒否することを確認。
2. [公開helper](publish_release.py)が監査基準tree・証跡・配布ZIP・メタデータ・clean checkoutを照合。
3. 対象タグのGitHub Releaseをdraftで作り、固定したassetをuploadした後に公開。
4. 既存Zenodo GitHub連携によるrecordを待ち、repo・版・著者ORCID・実DOIを照合。
5. Zenodoの実ZIPを取得し、全tracked pathと内容のGit blob SHA-1がタグと一致することを確認。
6. 照合後、実DOIをRelease本文と`ZENODO_RECEIPT_v1.0.0.json` assetへ記録。

成功したかどうかは実際のRelease、workflow結果、公開recordで確認する。
途中失敗のときは自動で別recordを作ったり、タグを付け替えたりしない。
公開済みReleaseの同名assetは同一hashなら再利用し、不一致なら上書きを拒否する。
Zenodoの反映待ちで停止した場合は、既存workflowの再実行で同じ版の確認を継続できる。
recordのZIP照合完了までは、保存・DOIの確認済みとは報告しない。

公開後の追加確認は`.github/workflows/verify-zenodo.yml`を使える。
これはmain上の現行API対応コードで**既存のv1.0.0タグ**を検証する。
現行Zenodo APIのlanding-page欄`self_html`にも対応する。
Release・DOIを新たに作らず、タグのファイル一覧・bytesを比較対象に固定する。
公開済みタグの内容は変更しない。

## DOIの扱い

版DOIは特定のv1.0.0の引用に、concept DOIは版をまたぐ継続リンクに使う。
DOIは実recordから取得し、推測や予約番号の作成はしない。
Releaseのtag snapshotにDOIが未記載でも、公開後のmainに別commitで案内を追加できる。
その際もv1.0.0タグは移動しない。

## 過去の準備資料

Run19時点の未完成表示、公開前のlicense候補・初期mainの調査結果は
準備commit `b3c37dde24e808a21e4313a58337b34718528a8f` の文書に残っている。
それらを完成後の公開状態として扱わない。
