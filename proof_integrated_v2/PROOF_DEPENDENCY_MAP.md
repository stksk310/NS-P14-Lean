# V02の証明依存関係

式番号・節番号は [統合証明本文](NS_P14_INTEGRATED_PROOF_JA.md) に対応する。
旧資料の閉鎖ラベル、旧境界の結論、JSONのPASSを未証明公理として受け取る辺はない。

## 主定理からの経路

| 結論 | 直接の依存 | 基礎・外部入力・有限補題 |
|---|---|---|
|P14、第16節|e≤2の直接計算、第1.2節の三生成元定理、第9/11/13/14/15節|比較先は第1.3節のactual interval|
|ordinary・cut2/3、第9節|第2–8節のactual塔と資源列|Green、数値座標、直接Koszul、Tor完全列、ordinary容量|
|ordinary・e≥10、第11節|第10節のscalar帰着、第5節の同じ資源列|H23、6小rank比較、rank10 anchor、barrier正項恒等式、固定Dの正二次式|
|狭幅・e≥5、第13節|第12節の共通端点移行、W1のtarget容量|Kneser、BHP/EK、dense/one-gap、疎幅の多項式、e5構造分岐|
|N4、第14節|第12節E18/E24、N8距離和、N9socle、N13標準語|Kneser、SC、196組の有限補題、幅4の全m剰余表、TLOW|
|小ordinary、第15節|O1–O5 actual有限化、O8–O13共通最大点、O14–O18 tails|BHP/EK、83組・665比較、5本の有理anchor|

## 共通端点補題の内部

| 節・式 | 内容 | 用途 |
|---|---|---|
|12.1–12.2、E1–E5|次数・offset基底、C→G、有限M_rと座標|幅側・N4の同じsource|
|12.3–12.4、E6–E11|jdずつの競合、clamp、M∩T、周期停止、vの冪零|actual模型とrank0の保証|
|12.5、E12–E15|PC/PGの区別、端点homology(PG,PG+R,R)|Koszul移行|
|12.6、E16–E18|PC≤W、R≤min(W−u,u max(Hx−2,0))|全m,dの一様上界|
|12.7、E19–E21|実核のTor補償と一般qのBetti移行|商のBetti単調性を使わない比較|
|12.8、E22–E24|q2の単項式Artin商と四行上界|N4|
|12.9、E25–E29|incidence、次数2保持、Koszul単位minor|幅側の第一行・高次行|

## 公刊入力の適用先

| 入力 | 正確な識別・statementの置き場所 | 使用先 |
|---|---|---|
|Green|本文1.2(1)、Caviglia §1 (1.1)|§4の次数2cut|
|BHP/EK|本文1.2(2)、Juhnke-Kubitzke–Venturello Lemmas2–3|§13のdense lex、§15のtruncated lex|
|Kneser|本文1.2(3)、DeVos Theorem1|§13の距離和、§14 N6–N8|
|算術列公式＋接錐一致|本文1.2(4)、GSS Theorem4.1、HS Proposition2.5|TAR、TMIN、ORD、各actual target|
|Lan–Tu–Vu|本文1.2(5)、Theorem1.1|三生成元の狭幅|
|Savchev–Chen|本文1.2(6)、§4 Theorem8|N4の混合標準語N11–N13|

通常の基礎代数はKoszul複体、Tor長完全列、Hilbert syzygy、
自由解消のrank Euler式、有界スペクトル系列、Gröbner除法である。
任意標数性を有理数体でのrank計算から推測しない。

## 有限補題とコード

| 数学的対象 | 再計算するコード | 保存データ | 資格 |
|---|---|---|---|
|N4の196 oriented offset組|checks/n4/check_shorter_n4.py|certificates/n4/SHORTER_N4_CERTIFICATE.json|N21–N22の必須有限整数補題|
|196組の独立照合|checks/n4/referee_core_audit.py|audits/independent_n4_run.json|別の二計算法。493組版の追加回帰も含む|
|小ordinaryの83組と5tail|checks/verify_small_ordinary.py|certificates/small_ordinary.json|O14–O18と有限83組|
|固定cutoffとbarrier|checks/verify_scalar.py|certificates/scalar_arithmetic.json|恒等式・有限有理比較。351例診断は補助|
|幅側の表と恒等式|checks/verify_width.py|certificates/width_arithmetic.json|Fraction多項式の全係数比較|

各有限範囲が全sourceを代表する理由は本文で証明した。
この依存表はLean形式化の完了を表すものではない。
