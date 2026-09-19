example (P : Prop) : ¬¬¬ P → ¬ P := by
  -- ¬¬¬ P かつ P と仮定する
  intro hn3p hp

  -- ここで ¬¬ P が成り立つ
  have hn2p : ¬¬ P := by
    -- なぜなら、 ¬ P であると仮定したとき
    intro hnp
    -- 仮定の P と矛盾するから
    contradiction

  contradiction

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  -- ここで ¬¬ P が成り立つ
  have : ¬¬ P := by
    intro hnp
    contradiction

  guard_hyp this : ¬¬ P

  contradiction

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P) と仮定する
  intro h

  -- ここで、 ¬ P を示せば十分である
  suffices hyp : ¬ P from by
    -- なぜなら、 ¬ P が成り立つなら特に P ∨ ¬ P が成り立つので ..
    have : P ∨ ¬ P := by
      right
      exact hyp

    -- 最初の仮定と矛盾するから
    contradiction

  -- 無事ゴールを ¬ P に帰着できた

  -- 以下、 ¬ P を示す
  guard_target =ₛ ¬ P

  -- P であると仮定する
  intro hq

  -- このとき P ∨ ¬ P が成り立つ
  have : P ∨ ¬ P := by
    left
    exact hq

  -- これは矛盾
  contradiction
