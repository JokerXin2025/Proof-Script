import ProofScript

/-! ## `embed` 概略策略分支嵌入测试（④）

被嵌入定理的 script 证明里包含概略策略（`split_and` 产生 `left`/`right` 分支）。
`_embed` 重放时应触发 `foundStrategy` / `mergeStrategyBoxes` 路径，
把各分支子 box 合并进被嵌入证明的 `proof` 数组。 -/

#theorem conj_from_hyp (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := script
  split_and
  | left => provide hp
  | right => provide hq

#theorem demo_strat (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := script
  embed (conj_from_hyp P Q hp hq) as h
  provide h

/- 期望：demo_strat.json 的 embed 步骤 `proof` 数组为
   `['_goal_', 'split_and']`，其中 `split_and` 步骤含 `name`/`left`/`right` 字段，
   `left`/`right` 各自为 `['_goal_', 'provide']`。 -/
