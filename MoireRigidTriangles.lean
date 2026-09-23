import MoireTriangleTopology

namespace MoireRigidTriangles
open MoireGeometry MoireDimension MoireTriangleTopology MoireTriangleBoundary MoireTriangle
noncomputable section

def rigid (angle : ℝ) (shift point : ℂ) : ℂ := rotation angle point + shift

theorem rigid_continuous (angle : ℝ) (shift : ℂ) : Continuous (rigid angle shift) :=
  (rotation_isometry angle).continuous.add continuous_const

theorem rotation_inverse (angle : ℝ) (point : ℂ) : rotation (-angle) (rotation angle point) = point := by
  change Complex.exp (((-angle : ℝ) : ℂ) * Complex.I) *
    (Complex.exp ((angle : ℂ) * Complex.I) * point) = point
  rw [← mul_assoc, ← Complex.exp_add]
  have cancel : (((-angle : ℝ) : ℂ) * Complex.I) + (angle : ℂ) * Complex.I = 0 := by
    push_cast; ring
  rw [cancel]
  simp

theorem rigid_inverse (angle : ℝ) (shift point : ℂ) :
    rigid (-angle) (-rotation (-angle) shift) (rigid angle shift point) = point := by
  simp only [rigid, map_add, rotation_inverse]
  abel

theorem rigid_inverse_right (angle : ℝ) (shift point : ℂ) :
    rigid angle shift (rigid (-angle) (-rotation (-angle) shift) point) = point := by
  have inverse : rotation angle (rotation (-angle) point) = point := by
    simpa using rotation_inverse (-angle) point
  have inverse_shift : rotation angle (rotation (-angle) shift) = shift := by
    simpa using rotation_inverse (-angle) shift
  simp only [rigid, map_add, map_neg, inverse, inverse_shift]
  abel

theorem rigid_mix (angle : ℝ) (shift first second : ℂ) (t : ℝ) :
    rigid angle shift ((1 - t) • first + t • second) =
      (1 - t) • rigid angle shift first + t • rigid angle shift second := by
  simp [rigid, rotation, Complex.real_smul]
  ring

theorem vertex_normSq_sum (angle : ℝ) (shift : ℂ) :
    Complex.normSq (rigid angle shift (vertex 0)) +
      Complex.normSq (rigid angle shift (vertex 1)) +
      Complex.normSq (rigid angle shift (vertex 2)) = 3 + 3 * Complex.normSq shift := by
  have vertices_sum : vertex 0 + vertex 1 + vertex 2 = 0 := by
    apply Complex.ext <;> simp [vertex] <;> ring
  have rotated_sum : rotation angle (vertex 0) + rotation angle (vertex 1) +
      rotation angle (vertex 2) = 0 := by rw [← map_add, ← map_add, vertices_sum, map_zero]
  have norms : ∀ digit, Complex.normSq (rotation angle (vertex digit)) = 1 := by
    intro digit
    rw [Complex.normSq_eq_norm_sq]
    have equality := (rotation_isometry angle).dist_eq (vertex digit) 0
    simp only [map_zero, dist_zero_right, vertex_norm] at equality
    rw [equality]; norm_num
  unfold rigid
  simp only [Complex.normSq_add, norms]
  have cross : (rotation angle (vertex 0) * star shift).re +
      (rotation angle (vertex 1) * star shift).re +
      (rotation angle (vertex 2) * star shift).re = 0 := by
    rw [← Complex.add_re, ← Complex.add_re, ← add_mul, ← add_mul, rotated_sum]
    simp
  change _ = _ at cross
  simp only [Complex.star_def] at cross
  linarith

theorem vertex_not_interior (angle : ℝ) (shift : ℂ) :
    ∃ digit, triangleLevel (rigid angle shift (vertex digit)) ≤ 0 := by
  by_contra! all_positive
  have first := level_positive_norm_lt_one (all_positive 0)
  have second := level_positive_norm_lt_one (all_positive 1)
  have third := level_positive_norm_lt_one (all_positive 2)
  have identity := vertex_normSq_sum angle shift
  simp only [Complex.normSq_eq_norm_sq] at identity
  nlinarith [norm_nonneg (rigid angle shift (vertex 0)),
    norm_nonneg (rigid angle shift (vertex 1)), norm_nonneg (rigid angle shift (vertex 2)),
    sq_nonneg ‖shift‖]

theorem triangle_mix {first second : ℂ} (first_mem : first ∈ closedTriangle)
    (second_mem : second ∈ closedTriangle) {t : ℝ} (nonnegative : 0 ≤ t) (upper : t ≤ 1) :
    (1 - t) • first + t • second ∈ closedTriangle := by
  intro digit
  rw [barycentric_mix]
  exact add_nonneg (mul_nonneg (by linarith) (first_mem digit)) (mul_nonneg nonnegative (second_mem digit))

end
end MoireRigidTriangles
