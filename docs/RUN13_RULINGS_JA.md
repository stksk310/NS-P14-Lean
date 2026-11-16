# Run13で記録した判断（発生順）

1. Ruling: ユーザーが指定した既存work checkout・通常Pushを継続 — 別worktreeへの移動で固定Lean/依存を複製せず、既存成果との接続を保つ — 誤れば監査対象branchの取り違えになるためHEAD/remoteと旧hashを照合する。

2. Ruling: 基準92cbe8fの証明済みexportは再実装せず、component-mapの自然性を共通基盤として不足接続を追加する — coneの実分解を共有すれば短完全列・graded・base-changeに同じ写像を使える — 誤ればTor比較の可換式が別写像になり得るため各成分で照合する。

3. Ruling: koszulFunctorを「obj=実koszulList、map=実再帰koszulMap」のfield表示へ整理 — 以前はfunctor全体のxs-recursionのためobj一致が命題的で、同じ実写像の可換式に型transportが混入した。変数作用・微分・mapの再帰内容は保持 — 誤れば旧自然性/transportが変わるため全旧exportを再ビルド・回帰する。

4. Ruling: inherited extension gradingだけではactual L側の独立したorder-gradingとの同定を完成扱いにしない — レビューImportant1はTask6の要求に該当する — 無視すればactual graded Bettiの不変性を未証明のまま閉鎖してしまう。

5. Ruling: exactness acceptanceのModuleCat universeは意図した0を明示する — libraryはk σと加群universeを同じuで定義しており、テストの独立universe推論が原因 — 誤れば高universe対応を検査したと過大報告する。高universe renameはこのactual P14 scope外。

6. Final: Ruling: minimal resolution存在/全対象Tor-balancingは追加しない — given actual minimal coverから本物のresolutionとrank橋が証明済みで、存在を使う定理がない — 後続が存在を使う場合は別途供給が必要。

7. Final: Ruling: cut・局所化rank0・actual tower/connecting rank・harmonic initial ideal・公刊入力/最終P14は後続入力として保持 — 指令の責務境界に一致 — 後続でこれらを一般補題の仮定のまま最終P14に使うことは不可。

8. Final: Ruling: archive/progress/commit/pushは形式検証とfix完了後に実行 — 完成を先取りしない — 最後の公開まで未完ならrun完成とは報告しない。

9. Ruling: imported ConstantInfoの種別だけで数学公理と判定せず、Lean自身のcollectAxiomsと自己依存を検査する — コンパイラのproof-erasure stubと真正公理を区別する必要がある — 誤れば公理の混入を見逃すため、許容3公理以外・新宣言の自己依存・ソースの明示axiom/sorry等をすべて拒否し、exported_kindも原形保存する。

Deferred minors：なし。
