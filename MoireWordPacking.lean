import MoirePrefixGeometry
import Mathlib.Data.List.OfFn

namespace MoireWordPacking

open MoireGeometry MoireSection2 MoireEisenstein MoireLatticeWords

noncomputable def wordCenter {length : ℕ} (word : Fin length → Fin 3) : ℂ :=
  ((1 / 2 : ℝ) ^ length) • complexCoordinates (wordValue (List.ofFn word))

theorem word_coordinates_injective (length : ℕ) :
    Function.Injective (fun word : Fin length → Fin 3 => wordValue (List.ofFn word)) :=
  wordValue_injective.comp List.ofFn_injective

/-- At any level, at most 289 blue cylinders can have their centers within
twice that level's scale of a given point. -/
theorem nearby_words_card_le (length : ℕ) (words : Finset (Fin length → Fin 3)) (center : ℂ)
    (inside : ∀ word ∈ words, dist (wordCenter word) center ≤ 2 * (1 / 2 : ℝ) ^ length) :
    words.card ≤ 289 := by
  classical
  have positive : 0 < (1 / 2 : ℝ) ^ length := by positivity
  have lattice_bound : ∀ point ∈ words.image (fun word => wordValue (List.ofFn word)),
      ‖complexCoordinates point - (((1 / 2 : ℝ) ^ length)⁻¹ • center)‖ ≤ 2 := by
    intro point member
    obtain ⟨word, word_mem, rfl⟩ := Finset.mem_image.mp member
    have normalized : complexCoordinates (wordValue (List.ofFn word)) -
        (((1 / 2 : ℝ) ^ length)⁻¹ • center) =
        (((1 / 2 : ℝ) ^ length)⁻¹) • (wordCenter word - center) := by
      simp only [wordCenter, smul_sub, smul_smul, inv_mul_cancel₀ positive.ne', one_smul]
    rw [normalized, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive)]
    have bound := mul_le_mul_of_nonneg_left (inside word word_mem) (inv_nonneg.mpr positive.le)
    rw [dist_eq_norm] at bound
    exact bound.trans_eq (by field_simp)
  have card_bound := MoirePrefixGeometry.lattice_disk_card_le _ _ lattice_bound
  rwa [Finset.card_image_of_injective _ (word_coordinates_injective length)] at card_bound

end MoireWordPacking
