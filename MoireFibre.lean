import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # The zero fibre and the intersection have the same Hausdorff dimension

This statement uses mathlib's actual Hausdorff dimension, not a scalar
placeholder. Products use the maximum metric; that metric is bi-Lipschitz
equivalent to the Euclidean product metric in the manuscript.
-/

namespace MoireFibre

open MeasureTheory

variable {V : Type*} [MetricSpace V]

def zeroFibre (set : Set V) (rotate : V → V) : Set (V × V) :=
  {pair | pair.1 ∈ set ∧ pair.2 ∈ set ∧ pair.1 = rotate pair.2}

theorem graph_isometry (rotate : V → V) (rotation_isometry : Isometry rotate) :
    Isometry (fun point => (rotate point, point)) := by
  apply Isometry.of_dist_eq
  intro firstPoint secondPoint
  simp only [Prod.dist_eq, rotation_isometry.dist_eq, max_self]

omit [MetricSpace V] in
theorem zeroFibre_eq_graph_image (set : Set V) (rotate : V → V) :
    zeroFibre set rotate =
      (fun point => (rotate point, point)) '' {point | point ∈ set ∧ rotate point ∈ set} := by
  ext pair
  constructor
  · rintro ⟨first_mem, second_mem, first_eq⟩
    exact ⟨pair.2, ⟨second_mem, first_eq ▸ first_mem⟩, Prod.ext first_eq.symm rfl⟩
  · rintro ⟨point, ⟨point_mem, rotated_mem⟩, rfl⟩
    exact ⟨rotated_mem, point_mem, rfl⟩

omit [MetricSpace V] in
theorem intersection_eq_rotation_image (set : Set V) (rotate : V → V) :
    set ∩ rotate '' set = rotate '' {point | point ∈ set ∧ rotate point ∈ set} := by
  ext point
  constructor
  · rintro ⟨point_mem, preimage, preimage_mem, rfl⟩
    exact ⟨preimage, ⟨preimage_mem, point_mem⟩, rfl⟩
  · rintro ⟨preimage, ⟨preimage_mem, rotated_mem⟩, rfl⟩
    exact ⟨rotated_mem, preimage, preimage_mem, rfl⟩

/-- The Hausdorff-dimension conclusion of Proposition `prop:fibre`. -/
theorem zeroFibre_hausdorffDim (set : Set V) (rotate : V → V)
    (rotation_isometry : Isometry rotate) :
    dimH (zeroFibre set rotate) = dimH (set ∩ rotate '' set) := by
  rw [zeroFibre_eq_graph_image, intersection_eq_rotation_image,
    (graph_isometry rotate rotation_isometry).dimH_image,
    rotation_isometry.dimH_image]

end MoireFibre
