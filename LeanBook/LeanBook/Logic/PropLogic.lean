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

#eval ¬ True

#eval ¬ False

/-- P と仮定すると矛盾する、ということは ¬ P と等しい -/
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- P と ¬ P を同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬ P は P → False に等しいので、P を示せばよい
  apply hnp

  -- 仮定 hp : P があるので、証明終わり
  exact hp

/-- 対偶が元の命題と同値になることの、片方のケース -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P :=by
  -- Q ならば ¬ P を示したいの Q であったと仮定する
  intro hq

  -- ¬ P は P → False に等しいので、
  -- さらに P であったと仮定する
  intro hp

  -- 仮定 h : P → Q → False に適用して False が得られる
  exact h hp hq

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- 矛盾を示せばよい
  exfalso

  -- 仮定に矛盾があるので証明終わり
  contradiction

#eval True ↔ True

#eval True ↔ False

#eval False ↔ True

#eval False ↔ False

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  . apply h1
  . apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  -- 両方向を示すことで証明する
  constructor

  -- まず左から右を示す
  case mp =>
    intro h
    exact h hq

  -- 右から左を示す
  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h

  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P → Q が佗傺にあるので、P の代わりに Q を示せばよい
  rw [h]

  -- 仮定 hq : Q があるので、証明終わり
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

/-- 同地な命題は等しい -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

#eval True ∧ True

#eval True ∧ False

#eval False ∧ True

#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  . exact hp
  . exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

#eval True ∨ True

#eval True ∨ False

#eval False ∨ True

#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

/-- 3.1.8 練習問題 1問目 -/
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intros npq p
  cases npq with
  | inl np =>
    exfalso
    exact np p
  | inr q =>
    exact q

/-- 3.1.8 練習問題 2問目 解その一 -/
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  · intro npq
    constructor
    · intro p
      exact npq (Or.inl p)
    · intro q
      exact npq (Or.inr q)
  · intros npnq pq
    cases pq with
    | inl p =>
      exact npnq.left p
    | inr q =>
      exact npnq.right q

/-- 3.1.8 練習問題 2問目 解その二 -/
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  · intro npq
    constructor
    · intro p
      exact npq (Or.inl p)
    · intro q
      exact npq (Or.inr q)
  · intro ⟨np,nq⟩
    intro pq
    cases pq with
    | inl p =>
      exact np p
    | inr q =>
      exact nq q
