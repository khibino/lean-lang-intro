#check Prop

-- これは命題
#check (1 + 1 = 3 : Prop)

-- これは命題ではなく、命題への関数
#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

#check False

example : True := by trivial

example : True := by constructor

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

/-- 矛盾からは何でも示せる -/
example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
    trivial

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True

#eval True → False

#eval False → True

#eval False → False

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- P → Q が成り立つので、Q を示すには P を示せばよい
  apply h

  -- P の成立はわかっているので、証明終わり
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/-- 含意の導入。Q であることがわかっているなら、仮定を足しても正しい -/
example (P Q : Prop) (hq : Q) : P → Q := by
  -- P → Q を示したいので P であることを仮定する
  intro hp

  -- 後は Q を示せばよいが、これは仮定されていたのであった
  exact hq
