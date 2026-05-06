import Mathlib

def foo (ε : ℝ) : Prop := True
lemma t (ε : ℝ) : True := by
  by_cases hε : ε ≤ 0
  · have hε' : 2 * ε ≤ 0 := by
      nlinarith
    trivial
  · have hεpos : 0 < ε := lt_of_not_ge hε
    trivial
