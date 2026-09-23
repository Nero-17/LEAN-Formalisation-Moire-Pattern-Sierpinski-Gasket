import MoireTriangle
import MoireEisenstein

namespace MoireTriangleBounds

open MoireGeometry MoireTriangle

noncomputable def linearCoordinate (digit : Fin 3) : ℂ →L[ℝ] ℝ :=
  match digit with
  | 0 => 2 • Complex.reCLM
  | 1 => -Complex.reCLM + Real.sqrt 3 • Complex.imCLM
  | 2 => -Complex.reCLM - Real.sqrt 3 • Complex.imCLM

theorem barycentric_eq_linearCoordinate (digit : Fin 3) (point : ℂ) :
    barycentric digit point = (1 + linearCoordinate digit point) / 3 := by
  fin_cases digit <;> simp [barycentric, linearCoordinate] <;> ring

theorem functional_le_of_vertex_le (functional : ℂ →L[ℝ] ℝ) (bound : ℝ)
    (vertices_le : ∀ digit, functional (vertex digit) ≤ bound)
    {point : ℂ} (point_mem : point ∈ gasket) : functional point ≤ bound := by
  obtain ⟨address, rfl⟩ := point_mem
  have weights_summable : Summable (fun level : ℕ => (1 / 2 : ℝ) ^ (level + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  have weights_sum : (∑' level : ℕ, (1 / 2 : ℝ) ^ (level + 1)) = 1 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
    norm_num
  have bound_sum := Summable.tsum_mono
    (functional.summable (address_summable vertex address))
    (weights_summable.mul_right bound) (fun level => show
      functional ((1 / 2 : ℝ) ^ (level + 1) • vertex (address level)) ≤
        (1 / 2 : ℝ) ^ (level + 1) * bound by
      rw [map_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (vertices_le _) (by positivity))
  rw [← functional.map_tsum (address_summable vertex address), tsum_mul_right,
    weights_sum, one_mul] at bound_sum
  exact bound_sum

theorem linearCoordinate_vertex_bounds (digit cornerDigit : Fin 3) :
    -1 ≤ linearCoordinate digit (vertex cornerDigit) ∧
      linearCoordinate digit (vertex cornerDigit) ≤ 2 := by
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases digit <;> fin_cases cornerDigit <;>
    norm_num [linearCoordinate, vertex] <;> constructor <;> nlinarith [sqrt_sq]

theorem linearCoordinate_gasket_lower (digit : Fin 3) {point : ℂ}
    (point_mem : point ∈ gasket) : -1 ≤ linearCoordinate digit point := by
  have bound := functional_le_of_vertex_le (-linearCoordinate digit) 1
    (fun cornerDigit => by
      simp only [ContinuousLinearMap.neg_apply]
      linarith [(linearCoordinate_vertex_bounds digit cornerDigit).1]) point_mem
  simp only [ContinuousLinearMap.neg_apply] at bound
  linarith

theorem barycentric_gasket_nonneg (digit : Fin 3) {point : ℂ}
    (point_mem : point ∈ gasket) : 0 ≤ barycentric digit point := by
  rw [barycentric_eq_linearCoordinate]
  linarith [linearCoordinate_gasket_lower digit point_mem]

noncomputable def rotationCLM (angle : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.exp (angle * Complex.I) • ContinuousLinearMap.id ℝ ℂ

theorem rotationCLM_apply (angle : ℝ) (point : ℂ) :
    rotationCLM angle point = rotation angle point := rfl

theorem piThird_exp_re : (Complex.exp ((Real.pi : ℂ) / 3 * Complex.I)).re = 1 / 2 := by
  simpa using Complex.exp_ofReal_mul_I_re (Real.pi / 3)

theorem piThird_exp_im : (Complex.exp ((Real.pi : ℂ) / 3 * Complex.I)).im = Real.sqrt 3 / 2 := by
  simpa using Complex.exp_ofReal_mul_I_im (Real.pi / 3)

theorem rotated_vertex_bound (digit cornerDigit : Fin 3) :
    linearCoordinate digit (rotationCLM (Real.pi / 3) (vertex cornerDigit)) ≤ 1 := by
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases digit <;> fin_cases cornerDigit <;>
    simp [linearCoordinate, rotationCLM, vertex, Complex.mul_re, Complex.mul_im,
      piThird_exp_re, piThird_exp_im] <;> nlinarith [sqrt_sq]

theorem live_piThird_coordinate_bound (displacement : ℂ)
    (live : (MoireSection2.shiftedIntersection gasket (rotation (Real.pi / 3)) displacement).Nonempty)
    (digit : Fin 3) : linearCoordinate digit displacement ≤ 2 := by
  obtain ⟨bluePoint, blue_mem, redPoint, red_mem, equality⟩ := live
  have displacement_eq : displacement = rotationCLM (Real.pi / 3) redPoint - bluePoint := by
    rw [rotationCLM_apply]
    linear_combination equality
  have red_bound := functional_le_of_vertex_le
    ((linearCoordinate digit).comp (rotationCLM (Real.pi / 3))) 1
    (rotated_vertex_bound digit) red_mem
  have blue_bound := linearCoordinate_gasket_lower digit blue_mem
  rw [displacement_eq, map_sub]
  change linearCoordinate digit (rotationCLM (Real.pi / 3) redPoint) ≤ 1 at red_bound
  linarith

end MoireTriangleBounds
