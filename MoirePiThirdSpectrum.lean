import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace MoirePiThirdSpectrum

open scoped NNReal ENNReal

noncomputable def adjacency : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 1, 1; 2, 0, 0, 0; 2, 0, 0, 0; 2, 0, 0, 0]

theorem characteristic_evaluation (value : ℂ) :
    adjacency.charpoly.eval value = value ^ 2 * (value ^ 2 - 6) := by
  rw [Matrix.eval_charpoly]
  simp [adjacency, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.diagonal_apply,
    Matrix.scalar_apply, Matrix.sub_apply, Fin.succAbove]
  ring

theorem spectrum_eq : spectrum ℂ adjacency =
    {0, (Real.sqrt 6 : ℂ), -(Real.sqrt 6 : ℂ)} := by
  have sqrt_sq : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  ext value
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change adjacency.charpoly.eval value = 0 ↔ _
  rw [characteristic_evaluation, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)]
  have factor : value ^ 2 - 6 = (value - (Real.sqrt 6 : ℂ)) *
      (value + (Real.sqrt 6 : ℂ)) := by
    calc
      _ = value ^ 2 - (Real.sqrt 6 : ℂ) ^ 2 := by rw [sqrt_sq]
      _ = _ := by ring
  rw [factor, mul_eq_zero]
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg]

theorem spectral_radius : spectralRadius ℂ adjacency = ENNReal.ofReal (Real.sqrt 6) := by
  rw [spectralRadius, spectrum_eq]
  have norm_sqrt : ((‖(Real.sqrt 6 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Real.sqrt 6) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg 6)]
  apply le_antisymm
  · apply iSup_le
    intro value
    apply iSup_le
    intro member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    · simp
    · exact le_of_eq norm_sqrt
    · simpa only [nnnorm_neg] using le_of_eq norm_sqrt
  · rw [← norm_sqrt]
    exact le_iSup_of_le (Real.sqrt 6 : ℂ)
      (le_iSup_of_le (by simp : (Real.sqrt 6 : ℂ) ∈
        ({0, (Real.sqrt 6 : ℂ), -(Real.sqrt 6 : ℂ)} : Set ℂ)) le_rfl)

end MoirePiThirdSpectrum
