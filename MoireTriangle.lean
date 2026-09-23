import MoireDimension

namespace MoireTriangle

open MoireGeometry MoireSection2

noncomputable def barycentric (digit : Fin 3) (point : ℂ) : ℝ :=
  match digit with
  | 0 => (1 + 2 * point.re) / 3
  | 1 => (1 - point.re + Real.sqrt 3 * point.im) / 3
  | 2 => (1 - point.re - Real.sqrt 3 * point.im) / 3

theorem barycentric_sum (point : ℂ) :
    barycentric 0 point + barycentric 1 point + barycentric 2 point = 1 := by
  simp only [barycentric]
  ring

theorem barycentric_corner (digit cornerDigit : Fin 3) (point : ℂ) :
    barycentric digit (cornerMap vertex cornerDigit point) =
      (barycentric digit point + if digit = cornerDigit then 1 else 0) / 2 := by
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold cornerMap
  rw [← real_half_smul]
  fin_cases digit <;> fin_cases cornerDigit <;>
    simp [barycentric, vertex, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt_sq]

def openTriangle : Set ℂ := {point | ∀ digit, 0 < barycentric digit point}

theorem openTriangle_isOpen : IsOpen openTriangle := by
  have continuous_coordinate : ∀ digit, Continuous (barycentric digit) := by
    intro digit
    fin_cases digit <;> unfold barycentric <;> fun_prop
  simpa only [openTriangle, Set.setOf_forall] using
    isOpen_iInter_of_finite (fun digit =>
      isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
        (continuous_coordinate digit))

theorem openTriangle_nonempty : openTriangle.Nonempty := by
  refine ⟨0, ?_⟩
  intro digit
  fin_cases digit <;> norm_num [barycentric]

theorem corner_openTriangle_subset (cornerDigit : Fin 3) :
    cornerMap vertex cornerDigit '' openTriangle ⊆ openTriangle := by
  rintro _ ⟨point, point_mem, rfl⟩ digit
  rw [barycentric_corner]
  have coordinate_pos := point_mem digit
  split_ifs <;> linarith

theorem corner_openTriangle_disjoint (firstDigit secondDigit : Fin 3)
    (distinct : firstDigit ≠ secondDigit) :
    Disjoint (cornerMap vertex firstDigit '' openTriangle)
      (cornerMap vertex secondDigit '' openTriangle) := by
  apply Set.disjoint_left.mpr
  rintro point ⟨firstPoint, first_mem, first_eq⟩ ⟨secondPoint, second_mem, second_eq⟩
  have first_bound : 1 / 2 < barycentric firstDigit point := by
    rw [← first_eq, barycentric_corner]
    simp only [↓reduceIte]
    linarith [first_mem firstDigit]
  have second_bound : 1 / 2 < barycentric secondDigit point := by
    rw [← second_eq, barycentric_corner]
    simp only [↓reduceIte]
    linarith [second_mem secondDigit]
  have all_pos : ∀ digit, 0 < barycentric digit point :=
    corner_openTriangle_subset firstDigit ⟨firstPoint, first_mem, first_eq⟩
  have total := barycentric_sum point
  fin_cases firstDigit <;> fin_cases secondDigit <;>
    simp_all only [ne_eq, not_true_eq_false, Fin.reduceFinMk] <;>
    linarith [all_pos 0, all_pos 1, all_pos 2]

end MoireTriangle
