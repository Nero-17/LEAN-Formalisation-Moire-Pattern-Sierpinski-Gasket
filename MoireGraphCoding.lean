import MoireGraphGeometry
import Mathlib.Analysis.SpecificLimits.Basic

namespace MoireGraphCoding

open MoireGeometry MoireSection2 MoireDeterminization
open Filter Topology

noncomputable def prefixMap (address : ℕ → Fin 3) : ℕ → ℂ → ℂ
  | 0, point => point
  | length + 1, point => prefixMap address length (cornerMap vertex (address length) point)

theorem prefixMap_dist (address : ℕ → Fin 3) (length : ℕ) (first second : ℂ) :
    dist (prefixMap address length first) (prefixMap address length second) =
      (1 / 2 : ℝ) ^ length * dist first second := by
  induction length generalizing first second with
  | zero => simp [prefixMap]
  | succ length inductionHypothesis =>
      simp only [prefixMap, inductionHypothesis, MoireDimension.cornerMap_dist, pow_succ]
      ring

theorem addressPoint_prefix (address : ℕ → Fin 3) (length : ℕ) :
    addressPoint vertex address = prefixMap address length
      (addressPoint vertex (fun level => address (length + level))) := by
  induction length with
  | zero => simp [prefixMap]
  | succ length inductionHypothesis =>
      rw [inductionHypothesis]
      change prefixMap address length (addressPoint vertex (fun level => address (length + level))) =
        prefixMap address length (cornerMap vertex (address length)
          (addressPoint vertex (fun level => address (length + 1 + level))))
      congr 1
      rw [addressPoint_split]
      simp only [Nat.add_zero, cornerMap, ← real_half_smul, Nat.add_assoc,
        Nat.add_comm 1]

theorem prefix_image_subset (angle : ℝ) (address : ℕ → Fin 3)
    (states : ℕ → Finset ℂ)
    (edges : ∀ level, Edge vertex gasket (rotation angle) (states level)
      (address level) (states (level + 1))) (length : ℕ) :
    prefixMap address length '' stateIntersection gasket (rotation angle) (states length) ⊆
      stateIntersection gasket (rotation angle) (states 0) := by
  induction length with
  | zero => simpa [prefixMap] using (Set.Subset.rfl :
      stateIntersection gasket (rotation angle) (states 0) ⊆ _)
  | succ length inductionHypothesis =>
      rintro _ ⟨point, point_mem, rfl⟩
      apply inductionHypothesis
      refine ⟨cornerMap vertex (address length) point, ?_, rfl⟩
      rw [gasket_state_recursion]
      apply Set.mem_iUnion.mpr
      refine ⟨address length, point, ?_, rfl⟩
      simpa [(edges length).1] using point_mem

/-- Every infinite path in the actual live-state graph codes a point of the
represented initial intersection; this does not assume the coding conclusion. -/
theorem addressPoint_mem_of_path (angle : ℝ) (address : ℕ → Fin 3)
    (states : ℕ → Finset ℂ)
    (edges : ∀ level, Edge vertex gasket (rotation angle) (states level)
      (address level) (states (level + 1)))
    (nonempty : ∀ level, (stateIntersection gasket (rotation angle) (states level)).Nonempty) :
    addressPoint vertex address ∈ stateIntersection gasket (rotation angle) (states 0) := by
  choose point point_mem using nonempty
  have approximant_mem : ∀ length, prefixMap address length (point length) ∈
      stateIntersection gasket (rotation angle) (states 0) := fun length =>
    prefix_image_subset angle address states edges length ⟨point length, point_mem length, rfl⟩
  have distance_bound : ∀ length,
      dist (prefixMap address length (point length)) (addressPoint vertex address) ≤
        2 * (1 / 2 : ℝ) ^ length := by
    intro length
    rw [addressPoint_prefix address length, prefixMap_dist]
    have point_norm := MoireDimension.norm_le_one_of_mem_gasket
      (stateIntersection_subset gasket (rotation angle) _ (point_mem length))
    have tail_norm := MoireDimension.norm_le_one_of_mem_gasket
      (show addressPoint vertex (fun level => address (length + level)) ∈ gasket from ⟨_, rfl⟩)
    have tail_distance : dist (point length)
        (addressPoint vertex (fun level => address (length + level))) ≤ 2 := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left tail_distance
      (show 0 ≤ (1 / 2 : ℝ) ^ length by positivity)]
  have converges : Tendsto (fun length => prefixMap address length (point length)) atTop
      (𝓝 (addressPoint vertex address)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) distance_bound
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  exact (MoireGraphGeometry.stateIntersection_isCompact angle (states 0)).isClosed.mem_of_tendsto
    converges (Filter.Eventually.of_forall approximant_mem)

end MoireGraphCoding
