# 監査ZIP

成果物：`artifacts/NS_P14_LEAN_RUN13_PARTIAL_20261110.zip`。
ZIPのSHA256は同ディレクトリの `.zip.sha256` に記録する（自己参照を避けてZIP外）。

Run12 manifestのpayloadとそのmanifest、新規core/試験/検証script、今回の原稿台帳・進捗・指令・
未完宣言・再校正・監査記録を収録する。旧uploaded ZIPや過去artifact ZIPは入れ子にしない。

`MANIFEST_SHA256.json` はZIP内の全payloadを列挙する（manifest自身を除く）。
manifest自身もZIPに含む。作成後、全entryを解凍せずSHA256でmanifest照合した。

ZIP名のPARTIALと検証JSONのrun13_complete=falseを保持する。
通常Pushのcommit SHAは最終報告とgit履歴を参照する。ZIPをその自身のcommit SHAで再書換えしない。
