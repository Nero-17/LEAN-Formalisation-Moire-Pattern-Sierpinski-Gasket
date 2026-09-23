import MoireDeterminantSublevel
import MoireProjectionSeparation
import MoireSection3

namespace MoireAlmostEveryProjection

open MoireGeometry MoireWordPacking MoireSeparationGeometry MoireDeterminantSublevel
open MoireProjectionSeparation MeasureTheory Filter
open scoped ENNReal

abbrev FourWords (length : ℕ) :=
  ((Fin length → Fin 3) × (Fin length → Fin 3)) ×
    ((Fin length → Fin 3) × (Fin length → Fin 3))

def badPair (length : ℕ) (words : FourWords length) : Set ℝ :=
  {angle | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧ words.1.1 ≠ words.1.2 ∧ words.2.1 ≠ words.2.2 ∧
    |determinant (wordCenter words.1.1 - wordCenter words.1.2)
      (rotation angle (wordCenter words.2.1) - rotation angle (wordCenter words.2.2))| <
        (1 / 512 : ℝ) ^ length}

def badLevel (length : ℕ) : Set ℝ := ⋃ words : FourWords length, badPair length words

theorem badPair_volume (length : ℕ) (words : FourWords length) :
    volume (badPair length words) ≤ ENNReal.ofReal (9 * Real.pi) * (1 / 128 : ℝ≥0∞) ^ length := by
  by_cases first_distinct : words.1.1 = words.1.2
  · simp [badPair, first_distinct]
  by_cases second_distinct : words.2.1 = words.2.2
  · simp [badPair, second_distinct]
  have amplitude : (1 / 4 : ℝ) ^ length ≤
      ‖wordCenter words.1.1 - wordCenter words.1.2‖ *
        ‖wordCenter words.2.1 - wordCenter words.2.2‖ := by
    have lower := mul_le_mul (wordCenter_separated _ _ first_distinct)
      (wordCenter_separated _ _ second_distinct) (by positivity)
      (norm_nonneg (wordCenter words.1.1 - wordCenter words.1.2))
    have powers : (1 / 2 : ℝ) ^ length * (1 / 2 : ℝ) ^ length = (1 / 4 : ℝ) ^ length := by
      rw [← mul_pow]
      norm_num
    rwa [powers] at lower
  have estimate := determinant_sublevel_volume
    (wordCenter words.1.1 - wordCenter words.1.2)
    (wordCenter words.2.1 - wordCenter words.2.2)
    ((1 / 4 : ℝ) ^ length) ((1 / 128 : ℝ) ^ length) (by positivity) amplitude (by positivity)
  have threshold : (1 / 4 : ℝ) ^ length * (1 / 128 : ℝ) ^ length = (1 / 512 : ℝ) ^ length := by
    rw [← mul_pow]
    norm_num
  rw [threshold] at estimate
  have sets_eq : badPair length words = {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
      |determinant (wordCenter words.1.1 - wordCenter words.1.2)
        (rotation angle (wordCenter words.2.1 - wordCenter words.2.2))| < (1 / 512 : ℝ) ^ length} := by
    ext angle
    simp [badPair, first_distinct, second_distinct, map_sub]
  rw [sets_eq]
  have conversion : ENNReal.ofReal (9 * Real.pi * (1 / 128 : ℝ) ^ length) =
      ENNReal.ofReal (9 * Real.pi) * (1 / 128 : ℝ≥0∞) ^ length := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rwa [conversion] at estimate

theorem fourWords_card (length : ℕ) : Fintype.card (FourWords length) = 81 ^ length := by
  simp only [FourWords, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← mul_pow, ← mul_pow]
  norm_num

theorem badLevel_volume (length : ℕ) :
    volume (badLevel length) ≤ ENNReal.ofReal (9 * Real.pi) * (81 / 128 : ℝ≥0∞) ^ length := by
  calc
    _ ≤ ∑ words : FourWords length, volume (badPair length words) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _words : FourWords length, ENNReal.ofReal (9 * Real.pi) * (1 / 128 : ℝ≥0∞) ^ length :=
      Finset.sum_le_sum fun words _ => badPair_volume length words
    _ = (81 : ℝ≥0∞) ^ length * (ENNReal.ofReal (9 * Real.pi) * (1 / 128 : ℝ≥0∞) ^ length) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fourWords_card, Nat.cast_pow, Nat.cast_ofNat]
    _ = _ := by rw [mul_left_comm, ← mul_pow]; simp [div_eq_mul_inv]

/-- Almost every angle has one uniform determinant lower bound for all pairs
of distinct blue and red words at every sufficiently fine level. -/
theorem ae_determinant_bound : ∀ᵐ angle : ℝ,
    0 ≤ angle → angle ≤ 2 * Real.pi → ∀ᶠ length in atTop,
      ∀ first second : Fin length → Fin 3, first ≠ second →
      ∀ third fourth : Fin length → Fin 3, third ≠ fourth →
        (1 / 512 : ℝ) ^ length ≤ |determinant (wordCenter first - wordCenter second)
          (rotation angle (wordCenter third) - rotation angle (wordCenter fourth))| := by
  have summable_bound : (∑' length : ℕ,
      ENNReal.ofReal (9 * Real.pi) * (81 / 128 : ℝ≥0∞) ^ length) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact (tsum_geometric_lt_top.mpr (show (81 / 128 : ℝ≥0∞) < 1 from
      (ENNReal.div_lt_iff (by simp) (by simp)).mpr (by norm_num))).ne
  have eventually_good := MoireSection3.ae_eventually_not_mem_of_summable_measure_bound
    volume badLevel (fun length => ENNReal.ofReal (9 * Real.pi) * (81 / 128 : ℝ≥0∞) ^ length)
    summable_bound badLevel_volume
  filter_upwards [eventually_good] with angle good
  intro nonneg upper
  filter_upwards [good] with length outside
  intro first second different third fourth other_different
  by_contra! small
  apply outside
  exact Set.mem_iUnion.mpr ⟨((first,second),(third,fourth)), nonneg, upper, different, other_different, small⟩

/-- The all-directions projected separation lemma on one full angular period.
The full-measure set is chosen before quantifying over the direction. -/
theorem ae_projection_dichotomy : ∀ᵐ angle : ℝ, 0 ≤ angle → angle ≤ 2 * Real.pi →
    ∀ direction : ℂ, ‖direction‖ = 1 →
      ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction := by
  filter_upwards [ae_determinant_bound] with angle determinant_bound
  intro nonneg upper
  exact projection_dichotomy_of_determinant_bound angle (1 / 512) (by norm_num) (by norm_num)
    (determinant_bound nonneg upper)

end MoireAlmostEveryProjection
