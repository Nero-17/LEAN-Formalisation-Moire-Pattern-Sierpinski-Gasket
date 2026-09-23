import MoireGraphCoding
import MoireSpectralWeights

namespace MoireGraphCovers

open MoireGeometry MoireSection2 MoireDeterminization
open scoped Matrix.Norms.Operator

noncomputable section

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- One center for each labelled walk. Repeated centers are retained so that
the length records walks, rather than distinct geometric points. -/
def centers (edge : State → Fin 3 → State → Prop) : ℕ → State → List ℂ
  | 0, _ => [0]
  | length + 1, source => by
      classical
      exact (Finset.univ : Finset State).toList.flatMap fun target =>
        ((Finset.univ : Finset (Fin 3)).filter (fun digit => edge source digit target)).toList.flatMap
          fun digit => (centers edge length target).map (cornerMap vertex digit)

def adjacency (edge : State → Fin 3 → State → Prop) : Matrix State State ℕ := by
  classical
  exact fun source target => (Finset.univ.filter (fun digit => edge source digit target)).card

theorem centers_length (edge : State → Fin 3 → State → Prop) (length : ℕ) (source : State) :
    (centers edge length source).length = ∑ target, (adjacency edge ^ length) source target := by
  classical
  induction length generalizing source with
  | zero => simp [centers, Matrix.one_apply]
  | succ length ih =>
      simp only [centers, List.length_flatMap, List.length_map]
      simp only [ih]
      simp only [Finset.sum_map_toList, Finset.sum_const, nsmul_eq_mul]
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp [adjacency, Finset.mul_sum]

/-- The geometric recursion produces an explicit cover at every scale. -/
theorem centers_cover (edge : State → Fin 3 → State → Prop) (sets : State → Set ℂ)
    (bounded : ∀ source, ∀ point ∈ sets source, ‖point‖ ≤ 1)
    (recursion : ∀ source, sets source ⊆ ⋃ target, ⋃ digit,
      ⋃ (_ : edge source digit target), cornerMap vertex digit '' sets target)
    (length : ℕ) (source : State) :
    ∀ point ∈ sets source, ∃ center ∈ centers edge length source,
      dist point center ≤ (1 / 2 : ℝ) ^ length := by
  classical
  induction length generalizing source with
  | zero =>
      intro point member
      exact ⟨0, by simp [centers], by simpa using bounded source point member⟩
  | succ length ih =>
      intro point member
      obtain ⟨target, member⟩ := Set.mem_iUnion.mp (recursion source member)
      obtain ⟨digit, member⟩ := Set.mem_iUnion.mp member
      obtain ⟨legal, predecessor, predecessor_mem, rfl⟩ := Set.mem_iUnion.mp member
      obtain ⟨center, center_mem, bound⟩ := ih target predecessor predecessor_mem
      refine ⟨cornerMap vertex digit center, ?_, ?_⟩
      · simp only [centers, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
          true_and, Finset.mem_filter, List.mem_map]
        exact ⟨target, digit, legal, center, center_mem, rfl⟩
      · rw [MoireDimension.cornerMap_dist, pow_succ']
        exact mul_le_mul_of_nonneg_left bound (by norm_num)

/-- The graph used in the paper satisfies the hypotheses of the explicit cover. -/
theorem actual_graph_recursion (angle : ℝ)
    (source : {state // ReachableState vertex gasket (rotation angle) state}) :
    stateIntersection gasket (rotation angle) source.val ⊆
      ⋃ target : {state // ReachableState vertex gasket (rotation angle) state},
      ⋃ digit, ⋃ (_ : Edge vertex gasket (rotation angle) source.val digit target.val),
      cornerMap vertex digit '' stateIntersection gasket (rotation angle) target.val := by
  classical
  intro point member
  rw [gasket_state_recursion] at member
  obtain ⟨digit, predecessor, predecessor_mem, rfl⟩ := Set.mem_iUnion.mp member
  have nonempty : (successorState vertex gasket (rotation angle) source.val digit).Nonempty := by
    obtain ⟨displacement, displacement_mem, _⟩ := predecessor_mem
    exact ⟨displacement, displacement_mem⟩
  have legal : Edge vertex gasket (rotation angle) source.val digit
      (successorState vertex gasket (rotation angle) source.val digit) := ⟨rfl, nonempty⟩
  exact Set.mem_iUnion.mpr ⟨⟨_, ReachableState.step source.property digit legal⟩,
    Set.mem_iUnion.mpr ⟨digit, Set.mem_iUnion.mpr ⟨legal, predecessor, predecessor_mem, rfl⟩⟩⟩

end

end MoireGraphCovers
