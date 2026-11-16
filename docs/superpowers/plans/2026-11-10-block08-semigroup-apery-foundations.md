# Block08 Actual Numerical Semigroup and Apéry Foundations Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans without check-ins between internal tasks.

**Goal:** 実際の数値半群からmultiplicity、Apéry剰余分解、最小生成系、最長orderと数値座標の基盤を構成する。

**Architecture:** cofiniteなAddSubmonoid ℕを定義し、最小の正元をmultiplicityとして構成する。各剰余の最小元を実際の半群内で取り、有限Apéry集合と一意分解を証明する。原子集合から最小生成系と埋込次元を作り、最長分解長とApéry次数計数・terminal/head数値対応へ進む。

**Tech Stack:** 固定Lean/mathlib revision。Block01–07の証明・テストを保持する。

**Spec:** V02 §2、V03 O_COORDの数値座標、SO1のactual Apéry/atom入力、計画M01。

## Global Constraints

- multiplicityや最小代表の存在・一意性を仮定せず、cofinitenessとℕの順序から構成する。
- 導入する数値orderをactual completed-semigroup tangent coneの次数と同一視する環同値は未完として明示する。
- sorry・追加数学axiomを使わず、Block02のIsAperyMinへ実際に接続する。
- 証明の表現変更・最終原稿への反映事項は対応台帳へ残す。
- 30分〜1時間程度のまとまった作業を目安に、複数ファイル・回帰・レビュー・Pushまで実行する。

## Review Focus

conductor=0、multiplicity=1、剰余0、半群要素0、自然数減算の切り捨て、最長分解の存在・有限性。

### Task 1: 半群とApéry座標

- [x] cofinite半群とactual multiplicityを定義・構成する。
- [x] 全剰余のApéry最小元、集合濃度m、一意分解x=ω+qmを証明する。
- [x] predecessor不在の特徴付けを証明する。

### Task 2: 最小生成系とorder

- [x] actual原子を有限集合として構成し、生成性・最小性・e≤mを証明する。
- [x] 最長正元分解長、上界、超加法性、0/atom/mのorderを証明する。

### Task 3: 数値座標の接続

- [x] Apéry次数0/1と原子の関係、残りの濃度m−eを証明する。
- [x] terminalと非Apéry x-headの数値対応を構成する。

### Task 4: 検証・監査・Push

- [x] 実半群の例、退化境界、既存7Block回帰と全公理依存を検査する。
- [ ] 独立レビュー・原稿対応・manifest・ZIPを保存し、Pushとremote SHAを確認する。

## 実行記録

基点は `51c558e1fe7b264edab204d389e7f2e6226e3096`。
6ファイル・85定理、最長orderが原子表示長であることの同値、全Apéry元order≤δ+1、
terminal/head全単射と同jumpのlive条件まで実装した。
ℕ、⟨3,4⟩、⟨6,7,15⟩の実半群テストと、既存7Blockを含む17コマンドが成功した。
レビュー担当も独立にテストをコンパイルし、正しさの重要な指摘はない。
提案された全単射定義の公理依存検査も追加し、新規86＋既存106件と全17項目の再検証が通過した。

実装判断：orderを一度「正元分解の最長」として構成し、最長の各因子が原子であると証明した。
原稿の最長生成元表示長との一致は定理であり、仮定ではない。対応台帳A10参照。
数値terminal/headとactual環の基底を混同せず、環・加群同定は未完として残す。
