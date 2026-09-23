import MoireGraphCoding

namespace MoirePrefixGeometry

open MoireGeometry MoireSection2 MoireGraphCoding MoireLatticeWords MoireEisenstein

theorem prefixMap_affine (address : ℕ → Fin 3) (length : ℕ) (point : ℂ) :
    prefixMap address length point =
      ((1 / 2 : ℝ) ^ length) • point + prefixMap address length 0 := by
  induction length generalizing point with
  | zero => simp [prefixMap]
  | succ length ih =>
      have zero_eq : prefixMap address (length + 1) 0 =
          ((1 / 2 : ℝ) ^ length) • cornerMap vertex (address length) 0 +
            prefixMap address length 0 := by rw [prefixMap, ih]
      rw [prefixMap, ih, zero_eq]
      simp only [cornerMap, ← real_half_smul, smul_add, smul_smul,
        zero_add, pow_succ]
      module

/-- Every level-n center is exactly a rescaled Eisenstein lattice point. -/
theorem prefixMap_center_coordinates (address : ℕ → Fin 3) (length : ℕ) :
    prefixMap address length 0 = ((1 / 2 : ℝ) ^ length) •
      complexCoordinates (wordValue (addressPrefix address length)) := by
  induction length with
  | zero => simp [prefixMap]
  | succ length ih =>
      rw [prefixMap, prefixMap_affine, ih, addressPrefix_succ,
        wordValue_append_singleton, map_add, map_nsmul, MoireConcrete.complexCoordinates_vertex]
      simp only [cornerMap, zero_add, ← real_half_smul, smul_smul, smul_add, pow_succ,
        nsmul_eq_mul]
      apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring

/-- The tail of the address places its point within the corresponding small
triangle's circumdisk. -/
theorem addressPoint_center_dist (address : ℕ → Fin 3) (length : ℕ) :
    dist (addressPoint vertex address) (prefixMap address length 0) ≤ (1 / 2 : ℝ) ^ length := by
  rw [addressPoint_prefix address length, prefixMap_dist, dist_zero_right]
  exact (mul_le_mul_of_nonneg_left (MoireDimension.norm_le_one_of_mem_gasket
    (show addressPoint vertex (fun level => address (length + level)) ∈ gasket from ⟨_, rfl⟩))
    (by positivity)).trans_eq (mul_one _)

/-- The two integer coordinates are uniformly controlled by the Euclidean norm. -/
theorem lattice_coordinate_norm_bounds (point : LatticePoint) :
    |(point.1 : ℝ)| ≤ 2 * ‖complexCoordinates point‖ ∧
      |(point.2 : ℝ)| ≤ 2 * ‖complexCoordinates point‖ := by
  have real_bound := Complex.abs_re_le_norm (complexCoordinates point)
  have imag_bound := Complex.abs_im_le_norm (complexCoordinates point)
  have sqrt_lower : 1 ≤ Real.sqrt 3 := by
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]
  have real_formula : (complexCoordinates point).re = point.1 - (point.2 : ℝ) / 2 := by
    simp [complexCoordinates, Complex.mul_re, omega]
    ring
  have imag_formula : (complexCoordinates point).im = (point.2 : ℝ) * (Real.sqrt 3 / 2) := by
    simp [complexCoordinates, Complex.mul_im, omega]
  rw [imag_formula, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 3 / 2)] at imag_bound
  have second_bound : |(point.2 : ℝ)| ≤ 2 * ‖complexCoordinates point‖ := by
    nlinarith [abs_nonneg (point.2 : ℝ)]
  refine ⟨?_, second_bound⟩
  have split : (point.1 : ℝ) = (complexCoordinates point).re + (point.2 : ℝ) / 2 := by
    rw [real_formula]
    ring
  calc
    |(point.1 : ℝ)| = |(complexCoordinates point).re + (point.2 : ℝ) / 2| := congrArg abs split
    _ ≤ |(complexCoordinates point).re| + |(point.2 : ℝ) / 2| := abs_add_le _ _
    _ ≤ 2 * ‖complexCoordinates point‖ := by rw [abs_div]; norm_num; linarith

/-- A fixed Euclidean disk meets only a uniformly bounded number of lattice
points. The deliberately loose constant avoids irrelevant optimal packing. -/
theorem lattice_disk_card_le (points : Finset LatticePoint) (center : ℂ)
    (inside : ∀ point ∈ points, ‖complexCoordinates point - center‖ ≤ 2) :
    points.card ≤ 289 := by
  classical
  by_cases empty : points = ∅
  · simp [empty]
  obtain ⟨base, base_mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have difference_bounds : ∀ point ∈ points,
      point - base ∈ (Finset.Icc (-8 : ℤ) 8) ×ˢ (Finset.Icc (-8 : ℤ) 8) := by
    intro point member
    have distance_bound : ‖complexCoordinates (point - base)‖ ≤ 4 := by
      rw [map_sub]
      have decomposition : complexCoordinates point - complexCoordinates base =
          (complexCoordinates point - center) + (center - complexCoordinates base) := by ring
      rw [decomposition]
      have reverse_bound : ‖center - complexCoordinates base‖ ≤ 2 := by
        rw [norm_sub_rev]
        exact inside base base_mem
      exact (norm_add_le _ _).trans (by linarith [inside point member])
    obtain ⟨first, second⟩ := lattice_coordinate_norm_bounds (point - base)
    have first_bounds : (-8 : ℝ) ≤ ((point - base).1 : ℝ) ∧
        ((point - base).1 : ℝ) ≤ 8 := abs_le.mp (first.trans (by linarith))
    have second_bounds : (-8 : ℝ) ≤ ((point - base).2 : ℝ) ∧
        ((point - base).2 : ℝ) ≤ 8 := abs_le.mp (second.trans (by linarith))
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact_mod_cast And.intro first_bounds second_bounds
  have subset : points.image (fun point => point - base) ⊆
      (Finset.Icc (-8 : ℤ) 8) ×ˢ (Finset.Icc (-8 : ℤ) 8) := by
    intro target member
    obtain ⟨point, point_mem, rfl⟩ := Finset.mem_image.mp member
    exact difference_bounds point point_mem
  have card_bound := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ (show Function.Injective
    (fun point : LatticePoint => point - base) from fun _ _ equal => by
      simpa using congrArg (fun point : LatticePoint => point + base) equal)] at card_bound
  norm_num at card_bound ⊢
  exact card_bound

end MoirePrefixGeometry
