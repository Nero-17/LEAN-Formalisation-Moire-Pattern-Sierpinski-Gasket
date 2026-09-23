import MoireAlmostEveryProjection

namespace MoireAlmostEverySeparation

open MoireGeometry MoireWordPacking MoireSeparationGeometry MoireProjectionSeparation
open MoireAlmostEveryProjection MeasureTheory Filter

theorem determinant_le_four_norm_sub (first second : ℂ) (bound : ‖second‖ ≤ 2) :
    |determinant first second| ≤ 4 * ‖first - second‖ := by
  have identity : determinant first second = determinant (first - second) second := by
    simp only [determinant, Complex.sub_re, Complex.sub_im]
    ring
  rw [identity]
  have estimate := determinant_le_projections 1 (first - second) second (by simp)
  have first_projection : |projection 1 (first - second)| ≤ ‖first - second‖ := by
    simpa [projection] using Complex.abs_re_le_norm (first - second)
  have second_projection : |projection 1 second| ≤ ‖second‖ := by
    simpa [projection] using Complex.abs_re_le_norm second
  have one := mul_le_mul_of_nonneg_right first_projection (norm_nonneg second)
  have two := mul_le_mul_of_nonneg_left second_projection (norm_nonneg (first - second))
  have three := mul_le_mul_of_nonneg_left bound (norm_nonneg (first - second))
  nlinarith

noncomputable def differenceTranslation (angle : ℝ) {length : ℕ}
    (word : Fin length → Fin 3 × Fin 3) : ℂ :=
  wordCenter (fun k => (word k).1) - rotation angle (wordCenter (fun k => (word k).2))

def DifferenceExponentiallySeparated (angle : ℝ) : Prop :=
  ∃ rate : ℝ, 0 < rate ∧ rate < 1 ∧ ∃ᶠ length in atTop,
    ∀ first second : Fin length → Fin 3 × Fin 3, first ≠ second →
      rate ^ length ≤ ‖differenceTranslation angle first - differenceTranslation angle second‖

theorem difference_separation_of_determinant_bound (angle : ℝ)
    (determinants : ∀ᶠ length in atTop,
      ∀ first second : Fin length → Fin 3, first ≠ second →
      ∀ third fourth : Fin length → Fin 3, third ≠ fourth →
        (1 / 512 : ℝ) ^ length ≤ |determinant (wordCenter first - wordCenter second)
          (rotation angle (wordCenter third) - rotation angle (wordCenter fourth))|) :
    DifferenceExponentiallySeparated angle := by
  refine ⟨1 / 4096, by norm_num, by norm_num, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [determinants, eventually_gt_atTop 0] with length bound length_pos
  intro first second different
  have not_both : (fun k => (first k).1) ≠ (fun k => (second k).1) ∨
      (fun k => (first k).2) ≠ (fun k => (second k).2) := by
    by_contra! both
    apply different
    funext k
    exact Prod.ext (congrFun both.1 k) (congrFun both.2 k)
  have small_scale : (1 / 4096 : ℝ) ^ length ≤ (1 / 2 : ℝ) ^ length :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  by_cases blue_equal : (fun k => (first k).1) = (fun k => (second k).1)
  · have red_different := not_both.resolve_left (not_not.mpr blue_equal)
    have lower := wordCenter_separated _ _ red_different
    have equality : differenceTranslation angle first - differenceTranslation angle second =
        -(rotation angle (wordCenter (fun k => (first k).2)) -
          rotation angle (wordCenter (fun k => (second k).2))) := by
      unfold differenceTranslation
      rw [blue_equal]
      ring
    rw [equality, norm_neg, ← dist_eq_norm, (rotation_isometry angle).dist_eq, dist_eq_norm]
    exact small_scale.trans lower
  by_cases red_equal : (fun k => (first k).2) = (fun k => (second k).2)
  · have equality : differenceTranslation angle first - differenceTranslation angle second =
        wordCenter (fun k => (first k).1) - wordCenter (fun k => (second k).1) := by
      unfold differenceTranslation
      rw [red_equal]
      ring
    rw [equality]
    exact small_scale.trans (wordCenter_separated _ _ blue_equal)
  have determinant_lower := bound _ _ blue_equal _ _ red_equal
  have red_norm : ‖rotation angle (wordCenter (fun k => (first k).2)) -
      rotation angle (wordCenter (fun k => (second k).2))‖ ≤ 2 := by
    rw [← dist_eq_norm, (rotation_isometry angle).dist_eq, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      linarith [wordCenter_norm_le_one length (fun k => (first k).2),
        wordCenter_norm_le_one length (fun k => (second k).2)])
  have determinant_upper := determinant_le_four_norm_sub
    (wordCenter (fun k => (first k).1) - wordCenter (fun k => (second k).1))
    (rotation angle (wordCenter (fun k => (first k).2)) -
      rotation angle (wordCenter (fun k => (second k).2))) red_norm
  have equality : wordCenter (fun k => (first k).1) - wordCenter (fun k => (second k).1) -
      (rotation angle (wordCenter (fun k => (first k).2)) -
        rotation angle (wordCenter (fun k => (second k).2))) =
      differenceTranslation angle first - differenceTranslation angle second := by
    unfold differenceTranslation
    ring
  rw [equality] at determinant_upper
  have smaller := divided_power_le (1 / 512) (by norm_num) length_pos
  norm_num at smaller
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 512) length]

/-- Almost-everywhere exponential separation of the nine-map difference system,
on one period, proved from concrete angular estimates and Borel–Cantelli. -/
theorem ae_difference_exponential_separation : ∀ᵐ angle : ℝ,
    0 ≤ angle → angle ≤ 2 * Real.pi → DifferenceExponentiallySeparated angle := by
  filter_upwards [ae_determinant_bound] with angle determinant_bound
  intro nonneg upper
  exact difference_separation_of_determinant_bound angle (determinant_bound nonneg upper)

end MoireAlmostEverySeparation
