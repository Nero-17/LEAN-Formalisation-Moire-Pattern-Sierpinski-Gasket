import MoireSeparationGeometry
import MoireIntersectionCounting

namespace MoireProjectionSeparation

open MoireGeometry MoireSection2 MoireWordPacking MoireGraphCoding
open MoireSeparationGeometry Filter

theorem prefixMap_norm_le_one (address : ℕ → Fin 3) (length : ℕ) {point : ℂ}
    (bound : ‖point‖ ≤ 1) : ‖prefixMap address length point‖ ≤ 1 := by
  induction length generalizing point with
  | zero => exact bound
  | succ length inductionHypothesis =>
      apply inductionHypothesis
      change ‖(1 / 2 : ℚ) • (point + vertex (address length))‖ ≤ 1
      rw [← real_half_smul, norm_smul, Real.norm_eq_abs]
      have estimate := norm_add_le point (vertex (address length))
      rw [MoireDimension.vertex_norm] at estimate
      norm_num
      linarith

theorem wordCenter_norm_le_one (length : ℕ) (word : Fin length → Fin 3) : ‖wordCenter word‖ ≤ 1 := by
  let address : ℕ → Fin 3 := fun k => if h : k < length then word ⟨k,h⟩ else 0
  have restriction : (fun k : Fin length => address k) = word := by
    funext k
    simp [address]
  rw [← restriction, MoireIntersectionCounting.center_prefix]
  exact prefixMap_norm_le_one address length (by simp)

theorem wordCenter_separated {length : ℕ} (first second : Fin length → Fin 3)
    (different : first ≠ second) :
    (1 / 2 : ℝ) ^ length ≤ ‖wordCenter first - wordCenter second‖ := by
  have nonzero : MoireLatticeWords.wordValue (List.ofFn first) -
      MoireLatticeWords.wordValue (List.ofFn second) ≠ 0 := by
    intro equality
    exact different (word_coordinates_injective length (sub_eq_zero.mp equality))
  have lower := one_le_norm_lattice nonzero
  have equality : wordCenter first - wordCenter second = ((1 / 2 : ℝ) ^ length) •
      MoireEisenstein.complexCoordinates (MoireLatticeWords.wordValue (List.ofFn first) -
        MoireLatticeWords.wordValue (List.ofFn second)) := by simp [wordCenter, map_sub, smul_sub]
  rw [equality, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simpa using mul_le_mul_of_nonneg_left lower (by positivity : 0 ≤ (1 / 2 : ℝ) ^ length)

def Separated {ι : Type*} (translations : ι → ℂ) (direction : ℂ) (threshold : ℝ) : Prop :=
  ∀ first second, first ≠ second → threshold ≤ |projection direction (translations first - translations second)|

/-- Uniform determinant separation forces separation of at least one projected
factor at that same scale; the exceptional set does not depend on direction. -/
theorem separated_or_separated {ι κ : Type*} (first : ι → ℂ) (second : κ → ℂ)
    (first_bounded : ∀ i j, ‖first i - first j‖ ≤ 2)
    (second_bounded : ∀ i j, ‖second i - second j‖ ≤ 2)
    (threshold : ℝ) (positive : 0 < threshold)
    (determinants : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      threshold ≤ |determinant (first i - first j) (second k - second l)|)
    (direction : ℂ) (unit : ‖direction‖ = 1) :
    Separated first direction (threshold / 8) ∨ Separated second direction (threshold / 8) := by
  by_contra! neither
  obtain ⟨i,j,different,small⟩ : ∃ i j, i ≠ j ∧
      |projection direction (first i - first j)| < threshold / 8 := by
    simpa only [Separated, not_forall, _root_.not_imp, not_le, exists_prop] using neither.1
  obtain ⟨k,l,other_different,other_small⟩ : ∃ k l, k ≠ l ∧
      |projection direction (second k - second l)| < threshold / 8 := by
    simpa only [Separated, not_forall, _root_.not_imp, not_le, exists_prop] using neither.2
  have upper := determinant_le_projections direction (first i - first j) (second k - second l) unit
  have lower := determinants i j different k l other_different
  have first_product := mul_le_mul_of_nonneg_left (second_bounded k l)
    (abs_nonneg (projection direction (first i - first j)))
  have second_product := mul_le_mul_of_nonneg_right (first_bounded i j)
    (abs_nonneg (projection direction (second k - second l)))
  nlinarith

def ExponentiallySeparated (translations : (length : ℕ) → (Fin length → Fin 3) → ℂ)
    (direction : ℂ) : Prop :=
  ∃ rate : ℝ, 0 < rate ∧ rate < 1 ∧ ∃ᶠ length in atTop,
    Separated (translations length) direction (rate ^ length)

theorem divided_power_le (rate : ℝ) (nonneg : 0 ≤ rate) {length : ℕ} (positive : 0 < length) :
    (rate / 8) ^ length ≤ rate ^ length / 8 := by
  obtain ⟨length, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have eight_le : (8 : ℝ) ≤ 8 ^ (length + 1) := by
    rw [pow_succ]
    nlinarith [show (1 : ℝ) ≤ 8 ^ length from one_le_pow₀ (by norm_num)]
  rw [div_pow]
  exact div_le_div_of_nonneg_left (pow_nonneg nonneg _) (by norm_num) eight_le

/-- The geometric part of the all-directions dichotomy for the actual gasket
cylinder translations, conditional only on the displayed determinant bound. -/
theorem projection_dichotomy_of_determinant_bound (angle rate : ℝ)
    (rate_pos : 0 < rate) (rate_lt_one : rate < 1)
    (determinants : ∀ᶠ length in atTop, ∀ first second : Fin length → Fin 3, first ≠ second →
      ∀ third fourth : Fin length → Fin 3, third ≠ fourth →
      rate ^ length ≤ |determinant (wordCenter first - wordCenter second)
        (rotation angle (wordCenter third) - rotation angle (wordCenter fourth))|) :
    ∀ direction : ℂ, ‖direction‖ = 1 →
      ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction := by
  intro direction unit
  have eventual : ∀ᶠ length in atTop,
      Separated (fun word : Fin length → Fin 3 => wordCenter word) direction ((rate / 8) ^ length) ∨
      Separated (fun word : Fin length → Fin 3 => rotation angle (wordCenter word)) direction ((rate / 8) ^ length) := by
    filter_upwards [determinants, eventually_gt_atTop 0] with length bound length_pos
    have blue_bound : ∀ first second : Fin length → Fin 3, ‖wordCenter first - wordCenter second‖ ≤ 2 := by
      intro first second
      exact (norm_sub_le _ _).trans (by linarith [wordCenter_norm_le_one length first, wordCenter_norm_le_one length second])
    have red_bound : ∀ first second : Fin length → Fin 3,
        ‖rotation angle (wordCenter first) - rotation angle (wordCenter second)‖ ≤ 2 := by
      intro first second
      simpa only [← dist_eq_norm, (rotation_isometry angle).dist_eq] using blue_bound first second
    have dichotomy := separated_or_separated _ _ blue_bound red_bound (rate ^ length)
      (pow_pos rate_pos _) bound direction unit
    have smaller := divided_power_le rate rate_pos.le length_pos
    exact dichotomy.imp (fun separated i j different => smaller.trans (separated i j different))
      (fun separated i j different => smaller.trans (separated i j different))
  have often := eventual.frequently
  rw [frequently_or_distrib] at often
  have small : rate / 8 < 1 := by linarith
  exact often.imp (fun separated => ⟨rate / 8, by positivity, small, separated⟩)
    (fun separated => ⟨rate / 8, by positivity, small, separated⟩)

end MoireProjectionSeparation
