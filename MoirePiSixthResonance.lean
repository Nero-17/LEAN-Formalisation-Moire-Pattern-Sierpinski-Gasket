import MoireDirectionalArithmetic
import Mathlib.NumberTheory.Real.Irrational

namespace MoirePiSixthResonance
open MoireDirectionalResonance MoireDirectionalArithmetic MoireAngles MoireEisenstein

theorem pi_sixth_directionallyResonant : DirectionallyResonant (Real.pi / 6) := by
  apply (directionallyResonant_iff_slope _).mpr
  right
  refine ⟨1 / 3, ?_⟩
  rw [Real.tan_pi_div_six]
  have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have nonzero : Real.sqrt 3 ≠ 0 := by positivity
  push_cast
  field_simp
  nlinarith [square]

theorem pi_sixth_not_resonant :
    Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) ∉ eisensteinField := by
  intro member
  obtain ⟨cosine, cosine_eq⟩ := (exp_mem_eisensteinField_iff_rational_trigonometric _).mp member |>.1
  rw [Real.cos_pi_div_six] at cosine_eq
  have irrational : Irrational (Real.sqrt 3) := by simpa using Nat.prime_three.irrational_sqrt
  apply irrational
  refine ⟨2 * cosine, ?_⟩
  push_cast
  linarith

end MoirePiSixthResonance
