# NS-P14 完全証明稿・N4独立監査

2026年11月9日。

[一本に統合した証明稿](NS_P14_COMPLETE_PROOF_JA.md) が最新版である。第12節に、前版で独立認証を保留していたN4を証明として組み込み、第13節で全域を合成した。数学的な資格は、公刊定理と厳密有限計算を用いる人間向けの計算支援証明。Lean形式化は未実施。

[監査・補強の記録](AUDIT_AND_REPAIRS_JA.md)、[独立査読記録](audits/FINAL_REFEREE.md)、[再実行記録](verification.json) を併せて参照できる。旧版の条件付き判定は履歴として保存し、本版の判定と区別する。

## 再実行

Python 3.10以上の標準ライブラリだけで動く。下記はこのディレクトリを作業ディレクトリとして実行する。

~~~sh
python3 -B checks/verify_scalar.py --diagnostic 210
python3 -B checks/verify_small_ordinary.py --out /tmp/p14_small_ordinary.json
python3 -B checks/check_width.py
python3 -B checks/check_harmonic.py --out /tmp/p14_harmonic.json
python3 -B checks/n4/independent_offset_audit.py > /tmp/p14_n4_offsets.json
python3 -B checks/n4/check_higher_rows.py --output /tmp/p14_n4_higher.json
python3 -B checks/n4/check_endpoint_model.py --max-u 10 --max-d 3 --m-excess 5 --degree 12
python3 -B checks/n4/check_boundary_family.py --regression --out /tmp/p14_n4_boundary.json
~~~

第1行用checkerは、コードと同じディレクトリに新しいgzip証書を生成する。保存済みの提出用証書は <code>certificates/n4/</code> に置く。高次行用の保存済み全証書はgzip圧縮されている。必要な有限補題は最初の6コマンドで再現する。最後の2コマンドは模型・小例外族に対する追加の独立回帰であり、無限範囲の証明の代わりにはしない。

全有限補題の根拠となる停止・範囲の完全性・無限tailは、統合稿内に記した。JSONのPASS表示やSHA-256だけを数学的証明として扱わない。
