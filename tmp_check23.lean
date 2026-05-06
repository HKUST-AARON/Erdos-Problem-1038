import Mathlib
variable {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Set.Ioo (-ε) ε)
#check (abs_lt.2 hx)
#check (abs_lt.mp (show |x| < ε from by sorry))
#check (show |x| < ε from (abs_lt.2 hx))
