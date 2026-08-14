/-- 自前で実装した自然数 -/
inductive MyNat where
  /-- ゼロ -/
  | zero
  /-- 後者関数 (n に対して n+1 を返す関数) -/
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ .zero

/-- 自前で定義した 1 -/
def MyNat.one := MyNat.succ .zero

/-- 自前で定義した 2 -/
def MyNat.two := MyNat.succ .one

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
    | .zero => m
    | .succ n => succ (add m n)

#check MyNat.add .one .one = .two

set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one
#reduce MyNat.two

/-- 1 + 1 = 2 の MyNat における証明 -/
example : MyNat.add .one .one = .two := by
  rfl

/- 2.2.7 練習問題 -/
/-- ゼロを右から足しても値は変わらない -/
example (n : MyNat) : MyNat.add n .zero = n := by
  rfl

-- example (n : MyNat) : MyNat.add .zero n = n := by
--   rfl
