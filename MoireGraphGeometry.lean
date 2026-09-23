import MoireCharacterisation
import MoireTriangleBounds

namespace MoireGraphGeometry

open MoireGeometry MoireSection2 MoireDeterminization MoireTriangle

theorem stateIntersection_isCompact (angle : ℝ) (state : Finset ℂ) :
    IsCompact (stateIntersection gasket (rotation angle) state) := by
  have representation : stateIntersection gasket (rotation angle) state =
      ⋃ displacement ∈ state, shiftedIntersection gasket (rotation angle) displacement := by
    ext point
    simp [stateIntersection]
  rw [representation]
  exact state.isCompact_biUnion (fun displacement _ =>
    MoireDimension.isCompact_shiftedIntersection angle displacement)

theorem reachable_state_nonempty (angle : ℝ) (nonneg : 0 ≤ angle)
    (upper : angle ≤ Real.pi / 3) (state : Finset ℂ)
    (reachable : ReachableState vertex gasket (rotation angle) state) :
    (stateIntersection gasket (rotation angle) state).Nonempty :=
  reachableState_represents_nonempty vertex gasket (rotation angle)
    (MoireNonempty.initial_intersection_nonempty angle nonneg upper) reachable

theorem state_in_closed_triangle (angle : ℝ) (state : Finset ℂ)
    {point : ℂ} (point_mem : point ∈ stateIntersection gasket (rotation angle) state)
    (digit : Fin 3) : 0 ≤ barycentric digit point :=
  MoireTriangleBounds.barycentric_gasket_nonneg digit
    (stateIntersection_subset gasket (rotation angle) state point_mem)

/-- The common open triangle is an open set condition witness for the actual graph.
The restriction to different labels is precisely justified by determinism. -/
theorem graph_open_set_condition :
    IsOpen openTriangle ∧ openTriangle.Nonempty ∧
      (∀ digit, cornerMap vertex digit '' openTriangle ⊆ openTriangle) ∧
      (∀ firstDigit secondDigit, firstDigit ≠ secondDigit →
        Disjoint (cornerMap vertex firstDigit '' openTriangle)
          (cornerMap vertex secondDigit '' openTriangle)) :=
  ⟨openTriangle_isOpen, openTriangle_nonempty, corner_openTriangle_subset,
    corner_openTriangle_disjoint⟩

theorem graph_distinct_edges_disjoint (angle : ℝ)
    (source firstTarget secondTarget : Finset ℂ) (firstDigit secondDigit : Fin 3)
    (firstEdge : Edge vertex gasket (rotation angle) source firstDigit firstTarget)
    (secondEdge : Edge vertex gasket (rotation angle) source secondDigit secondTarget)
    (distinct : (firstDigit, firstTarget) ≠ (secondDigit, secondTarget)) :
    Disjoint (cornerMap vertex firstDigit '' openTriangle)
      (cornerMap vertex secondDigit '' openTriangle) := by
  apply corner_openTriangle_disjoint
  intro digits_eq
  subst secondDigit
  apply distinct
  exact Prod.ext rfl (edge_deterministic vertex gasket (rotation angle) firstEdge secondEdge)

end MoireGraphGeometry
