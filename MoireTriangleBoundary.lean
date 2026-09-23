import MoireTriangleBounds
import MoireGraphCoding

namespace MoireTriangleBoundary
open MoireGeometry MoireSection2 MoireTriangle MoireTriangleBounds MoireDimension
open Filter Topology
noncomputable section

def closedTriangle : Set ℂ := {point | ∀ digit, 0 ≤ barycentric digit point}
def triangleBoundary : Set ℂ :=
  {point | point ∈ closedTriangle ∧ ∃ digit, barycentric digit point = 0}

theorem barycentric_reconstruct (point : ℂ) :
    ∑ digit : Fin 3, barycentric digit point • vertex digit = point := by
  have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp only [Fin.sum_univ_three]
  apply Complex.ext <;> simp [barycentric, vertex, Complex.smul_re, Complex.smul_im] <;>
    nlinarith [congrArg (fun t : ℝ => t * point.im) square]

theorem triangle_norm {point : ℂ} (member : point ∈ closedTriangle) : ‖point‖ ≤ 1 := by
  calc
    ‖point‖ = ‖∑ digit : Fin 3, barycentric digit point • vertex digit‖ :=
      congrArg norm (barycentric_reconstruct point).symm
    _ ≤ ∑ digit : Fin 3, ‖barycentric digit point • vertex digit‖ := norm_sum_le _ _
    _ = 1 := by
      simp only [norm_smul, vertex_norm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (member _), Fin.sum_univ_three]
      exact barycentric_sum point

theorem gasket_subset_triangle : gasket ⊆ closedTriangle := by
  intro point member digit
  exact barycentric_gasket_nonneg digit member

theorem barycentric_inverse_corner (digit corner : Fin 3) (point : ℂ) :
    barycentric digit ((2 : ℝ) • point - vertex corner) =
      2 * barycentric digit point - if digit = corner then 1 else 0 := by
  have inverse : cornerMap vertex corner ((2 : ℝ) • point - vertex corner) = point := by
    unfold cornerMap
    rw [← real_half_smul]
    module
  have identity := barycentric_corner digit corner ((2 : ℝ) • point - vertex corner)
  rw [inverse] at identity
  linarith

theorem boundary_predecessor {point : ℂ} (member : point ∈ triangleBoundary) :
    ∃ digit, ∃ parent ∈ triangleBoundary, point = cornerMap vertex digit parent := by
  obtain ⟨nonnegative, missing, missing_zero⟩ := member
  have large : ∃ digit, (1 / 2 : ℝ) ≤ barycentric digit point := by
    by_contra! none
    have total := barycentric_sum point
    fin_cases missing <;> simp only [Fin.reduceFinMk] at missing_zero <;>
      linarith [none 0, none 1, none 2]
  obtain ⟨digit, large⟩ := large
  have different : missing ≠ digit := by intro equality; rw [← equality, missing_zero] at large; norm_num at large
  refine ⟨digit, (2 : ℝ) • point - vertex digit, ⟨?_, missing, ?_⟩, ?_⟩
  · intro index
    rw [barycentric_inverse_corner]
    split_ifs with equality
    · subst index; linarith
    · linarith [nonnegative index]
  · rw [barycentric_inverse_corner, missing_zero, if_neg different]
    norm_num
  · unfold cornerMap
    rw [← real_half_smul]
    module

/-- A bounded set admitting a predecessor in itself lies in the actual address-series gasket. -/
theorem subset_gasket_of_predecessors (set : Set ℂ)
    (bounded : ∀ point ∈ set, ‖point‖ ≤ 1)
    (predecessor : ∀ point ∈ set, ∃ digit, ∃ parent ∈ set,
      point = cornerMap vertex digit parent) : set ⊆ gasket := by
  have approximations : ∀ n : ℕ, ∀ point ∈ set, ∃ approximate ∈ gasket,
      dist point approximate ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro point member
      refine ⟨vertex 0, vertex_mem_gasket 0, ?_⟩
      have bound := norm_sub_le point (vertex 0)
      rw [dist_eq_norm, pow_zero, mul_one]
      rw [vertex_norm] at bound
      linarith [bounded point member]
    | succ n ih =>
      intro point member
      obtain ⟨digit, parent, parent_mem, equality⟩ := predecessor point member
      obtain ⟨approximate, approximate_mem, close⟩ := ih parent parent_mem
      refine ⟨cornerMap vertex digit approximate, ?_, ?_⟩
      · rw [gasket_selfSimilar]
        exact Set.mem_iUnion.mpr ⟨digit, approximate, approximate_mem, rfl⟩
      · rw [equality, cornerMap_dist, pow_succ]
        linarith
  intro point member
  rw [← isCompact_gasket.isClosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro epsilon positive
  have tends : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  obtain ⟨n, small⟩ := (tends.eventually (gt_mem_nhds positive)).exists
  obtain ⟨approximate, approximate_mem, close⟩ := approximations n point member
  exact ⟨approximate, approximate_mem, close.trans_lt small⟩

theorem boundary_subset_gasket : triangleBoundary ⊆ gasket :=
  subset_gasket_of_predecessors triangleBoundary (fun _ member => triangle_norm member.1)
    (fun _ member => boundary_predecessor member)

end
end MoireTriangleBoundary
