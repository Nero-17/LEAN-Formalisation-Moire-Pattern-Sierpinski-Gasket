import MoireTriangleBoundary
import Mathlib.Topology.Order.IntermediateValue

namespace MoireTriangleTopology
open MoireGeometry MoireTriangle MoireTriangleBoundary MoireDimension Set
noncomputable section

def edge (first second : Fin 3) : Set ℂ :=
  (fun t : ℝ => (1 - t) • vertex first + t • vertex second) '' Icc 0 1

theorem barycentric_vertex (digit corner : Fin 3) :
    barycentric digit (vertex corner) = if digit = corner then 1 else 0 := by
  have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases digit <;> fin_cases corner <;> norm_num [barycentric, vertex] <;> nlinarith [square]

theorem barycentric_mix (digit : Fin 3) (first second : ℂ) (t : ℝ) :
    barycentric digit ((1 - t) • first + t • second) =
      (1 - t) * barycentric digit first + t * barycentric digit second := by
  fin_cases digit <;> simp [barycentric, Complex.real_smul] <;> ring

theorem edge_subset_boundary (first second : Fin 3) (distinct : first ≠ second) :
    edge first second ⊆ triangleBoundary := by
  rintro _ ⟨t, ⟨nonnegative, upper⟩, rfl⟩
  constructor
  · intro digit
    rw [barycentric_mix, barycentric_vertex, barycentric_vertex]
    split_ifs <;> nlinarith
  · fin_cases first <;> fin_cases second <;> simp_all only [ne_eq, not_true_eq_false]
    all_goals first
      | (refine ⟨0, ?_⟩; rw [barycentric_mix]; norm_num [barycentric_vertex, Fin.ext_iff]; done)
      | (refine ⟨1, ?_⟩; rw [barycentric_mix]; norm_num [barycentric_vertex, Fin.ext_iff]; done)
      | (refine ⟨2, ?_⟩; rw [barycentric_mix]; norm_num [barycentric_vertex, Fin.ext_iff]; done)

theorem boundary_eq_edges : triangleBoundary = (edge 0 1 ∪ edge 1 2) ∪ edge 2 0 := by
  apply Subset.antisymm
  · intro point member
    have nonnegative := member.1
    obtain ⟨missing, zero⟩ := member.2
    have total := barycentric_sum point
    have reconstruction := barycentric_reconstruct point
    simp only [Fin.sum_univ_three] at reconstruction
    fin_cases missing
    · change barycentric 0 point = 0 at zero
      apply Or.inl ∘ Or.inr
      refine ⟨barycentric 2 point, ⟨nonnegative 2, ?_⟩, ?_⟩
      · linarith [nonnegative 1]
      · rw [zero, zero_smul, zero_add] at reconstruction
        have equality : 1 - barycentric 2 point = barycentric 1 point := by linarith
        simpa only [equality] using reconstruction
    · change barycentric 1 point = 0 at zero
      right
      refine ⟨barycentric 0 point, ⟨nonnegative 0, ?_⟩, ?_⟩
      · linarith [nonnegative 2]
      · rw [zero, zero_smul, add_zero] at reconstruction
        have equality : 1 - barycentric 0 point = barycentric 2 point := by linarith
        dsimp only
        rw [equality, add_comm]
        exact reconstruction
    · change barycentric 2 point = 0 at zero
      apply Or.inl ∘ Or.inl
      refine ⟨barycentric 1 point, ⟨nonnegative 1, ?_⟩, ?_⟩
      · linarith [nonnegative 0]
      · rw [zero, zero_smul, add_zero] at reconstruction
        have equality : 1 - barycentric 1 point = barycentric 0 point := by linarith
        simpa only [equality] using reconstruction
  · exact union_subset (union_subset (edge_subset_boundary 0 1 (by decide))
      (edge_subset_boundary 1 2 (by decide))) (edge_subset_boundary 2 0 (by decide))

theorem edge_preconnected (first second : Fin 3) : IsPreconnected (edge first second) :=
  isPreconnected_Icc.image _ (by fun_prop)

theorem vertex_left_edge (first second : Fin 3) : vertex first ∈ edge first second :=
  ⟨0, by norm_num, by simp⟩

theorem vertex_right_edge (first second : Fin 3) : vertex second ∈ edge first second :=
  ⟨1, by norm_num, by simp⟩

theorem boundary_preconnected : IsPreconnected triangleBoundary := by
  rw [boundary_eq_edges]
  exact IsPreconnected.union (vertex 0) (Or.inl (vertex_left_edge 0 1)) (vertex_right_edge 2 0)
    (IsPreconnected.union (vertex 1) (vertex_right_edge 0 1) (vertex_left_edge 1 2)
      (edge_preconnected 0 1) (edge_preconnected 1 2)) (edge_preconnected 2 0)

def triangleLevel (point : ℂ) : ℝ := min (barycentric 0 point)
  (min (barycentric 1 point) (barycentric 2 point))

theorem continuous_triangleLevel : Continuous triangleLevel := by
  unfold triangleLevel barycentric
  fun_prop

theorem mem_triangle_iff_level (point : ℂ) : point ∈ closedTriangle ↔ 0 ≤ triangleLevel point := by
  simp only [closedTriangle, mem_setOf_eq, triangleLevel, le_min_iff]
  exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ digit => by fin_cases digit <;> assumption⟩

theorem mem_boundary_iff_level (point : ℂ) : point ∈ triangleBoundary ↔ triangleLevel point = 0 := by
  constructor
  · rintro ⟨nonnegative, digit, zero⟩
    apply le_antisymm _ ((mem_triangle_iff_level point).mp nonnegative)
    fin_cases digit <;> simp only [triangleLevel, min_le_iff, zero] <;> aesop
  · intro zero
    refine ⟨(mem_triangle_iff_level point).mpr zero.ge, ?_⟩
    unfold triangleLevel at zero
    rcases min_cases (barycentric 0 point) (min (barycentric 1 point) (barycentric 2 point)) with h | h
    · exact ⟨0, h.1.symm.trans zero⟩
    · rcases min_cases (barycentric 1 point) (barycentric 2 point) with h' | h'
      · exact ⟨1, h'.1.symm.trans (h.1.symm.trans zero)⟩
      · exact ⟨2, h'.1.symm.trans (h.1.symm.trans zero)⟩

theorem vertex_boundary (digit : Fin 3) : vertex digit ∈ triangleBoundary := by
  rw [mem_boundary_iff_level]
  fin_cases digit <;> norm_num [triangleLevel, barycentric_vertex, Fin.ext_iff]

theorem level_positive_norm_lt_one {point : ℂ} (positive : 0 < triangleLevel point) : ‖point‖ < 1 := by
  have coordinates : 0 < barycentric 0 point ∧ 0 < barycentric 1 point ∧ 0 < barycentric 2 point := by
    simpa only [triangleLevel, lt_min_iff] using positive
  have identity : Complex.normSq point + 3 *
      (barycentric 0 point * barycentric 1 point + barycentric 0 point * barycentric 2 point +
        barycentric 1 point * barycentric 2 point) = 1 := by
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    simp only [Complex.normSq_apply, barycentric]
    nlinarith [congrArg (fun t : ℝ => t * point.im ^ 2) square]
  rw [Complex.normSq_eq_norm_sq] at identity
  nlinarith [mul_pos coordinates.1 coordinates.2.1,
    mul_pos coordinates.1 coordinates.2.2, mul_pos coordinates.2.1 coordinates.2.2]

end
end MoireTriangleTopology
