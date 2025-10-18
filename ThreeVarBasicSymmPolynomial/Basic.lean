import Mathlib.Tactic

theorem pairs_mul_add_triple_eq_sum_mul_pairs {R : Type*} [CommSemiring R] (a b c : R) :
  (a + b) * (b + c) * (c + a) + a*b*c
  = (a + b + c) * (a*b + b*c + c*a) := by

  have h₁ : (a + b) * (b + c) = a*b + a*c + b*b + b*c := by
    ring
  calc
    (a + b) * (b + c) * (c + a) + a*b*c
      = (a*b + a*c + b*b + b*c) * (c + a) + a*b*c := by
        simp [h₁]
    _ = ((a*b + a*c + b*b + b*c) * c)
        + ((a*b + a*c + b*b + b*c) * a) + a*b*c := by
          simp [mul_add, add_assoc]
    _ = (a*b*c + a*c*c + b*b*c + b*c*c)
        + (a*b*a + a*c*a + b*b*a + b*c*a) + a*b*c := by
          simp [add_mul, mul_assoc, add_comm, add_left_comm, add_assoc]
    _ = (a + b + c) * (a*b + b*c + c*a) := by
          ring
