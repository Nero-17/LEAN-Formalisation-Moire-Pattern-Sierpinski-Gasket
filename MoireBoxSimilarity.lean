import MoireBoxDimension

namespace MoireBoxSimilarity

open MoireBoxDimension MoireGeometry MoireSection2 MoireDeterminization Filter
open scoped NNReal

noncomputable def inverseCorner (digit : Fin 3) (point : ℂ) : ℂ :=
  (2 : ℝ) • point - vertex digit

theorem inverseCorner_corner (digit : Fin 3) (point : ℂ) :
    inverseCorner digit (cornerMap vertex digit point) = point := by
  unfold inverseCorner
  rw [cornerMap, ← real_half_smul, smul_smul]
  norm_num

theorem inverseCorner_dist (digit : Fin 3) (first second : ℂ) :
    dist (inverseCorner digit first) (inverseCorner digit second) = 2 * dist first second := by
  simp only [inverseCorner, dist_eq_norm, sub_sub_sub_cancel_right, ← smul_sub, norm_smul]
  norm_num

theorem inverse_cover (set : Set ℂ) (digit : Fin 3) (length : ℕ) (centers : List ℂ)
    (cover : Covers (cornerMap vertex digit '' set) (length + 1) centers) :
    Covers set length (centers.map (inverseCorner digit)) := by
  intro point member
  obtain ⟨center, center_mem, bound⟩ := cover (cornerMap vertex digit point) ⟨point, member, rfl⟩
  refine ⟨inverseCorner digit center, List.mem_map.mpr ⟨center, center_mem, rfl⟩, ?_⟩
  rw [← inverseCorner_corner digit point, inverseCorner_dist]
  have multiplied := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)
  exact multiplied.trans_eq (by rw [pow_succ]; ring)

theorem lowerExponent_corner (set : Set ℂ) (digit : Fin 3) (dimension : ℝ≥0)
    (lower : LowerExponent set dimension) : LowerExponent (cornerMap vertex digit '' set) dimension := by
  obtain ⟨constant, positive, bounds⟩ := lower
  obtain ⟨threshold, bounds⟩ := eventually_atTop.mp bounds
  have base_pos : 0 < (2 : ℝ) ^ (dimension : ℝ) := by positivity
  refine ⟨constant / (2 : ℝ) ^ (dimension : ℝ), div_pos positive base_pos,
    eventually_atTop.mpr ⟨threshold + 1, ?_⟩⟩
  intro length large centers cover
  have length_pos : 0 < length := by omega
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero length_pos.ne'
  have previous_large : threshold ≤ previous := by omega
  have bound := bounds previous previous_large (centers.map (inverseCorner digit))
    (inverse_cover set digit previous centers cover)
  simp only [List.length_map] at bound
  have coefficient : constant / (2 : ℝ) ^ (dimension : ℝ) *
      ((2 : ℝ) ^ (dimension : ℝ)) ^ (previous + 1) =
        constant * ((2 : ℝ) ^ (dimension : ℝ)) ^ previous := by
    rw [pow_succ]
    field_simp
  rw [coefficient]
  exact bound

theorem reachable_lowerExponent_initial (angle : ℝ) (state : Finset ℂ)
    (reachable : ReachableState vertex gasket (rotation angle) state)
    (dimension : ℝ≥0) (lower : LowerExponent (stateIntersection gasket (rotation angle) state) dimension) :
    LowerExponent (shiftedIntersection gasket (rotation angle) 0) dimension := by
  induction reachable with
  | initial => simpa using lower
  | @step source target previous digit edge ih =>
      apply ih
      have contained : cornerMap vertex digit '' stateIntersection gasket (rotation angle) target ⊆
          stateIntersection gasket (rotation angle) source := by
        intro point member
        rw [gasket_state_recursion angle source]
        exact Set.mem_iUnion.mpr ⟨digit, by simpa only [← edge.1] using member⟩
      exact lowerExponent_mono contained dimension
        (lowerExponent_corner _ digit dimension lower)

end MoireBoxSimilarity
