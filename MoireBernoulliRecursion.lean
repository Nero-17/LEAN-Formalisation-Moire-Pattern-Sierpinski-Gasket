import MoireDifferenceLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-! Splitting the first digit of an actual infinite Bernoulli address. -/
namespace MoireBernoulliRecursion

open MeasureTheory MoireGeometry MoireDifferenceMeasure
open scoped ENNReal
noncomputable section

def prepend {α : Type*} (pair : α × (ℕ → α)) : ℕ → α :=
  fun n => Nat.casesOn n pair.1 pair.2

theorem measurable_prepend {α : Type*} [MeasurableSpace α] :
    Measurable (prepend (α := α)) := by
  apply measurable_pi_lambda
  intro n
  cases n <;> simp only [prepend] <;> fun_prop

theorem prepend_law {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    (μ.prod (Measure.infinitePi (fun _ : ℕ => μ))).map prepend =
      Measure.infinitePi (fun _ : ℕ => μ) := by
  classical
  apply Measure.eq_infinitePi
  intro indices sets measurable_sets
  rw [Measure.map_apply measurable_prepend
    (MeasurableSet.pi indices.countable_toSet (fun n _ => measurable_sets n))]
  have boxes : prepend ⁻¹' Set.pi (↑indices) sets =
      (if 0 ∈ indices then sets 0 else Set.univ) ×ˢ
        Set.pi (↑(indices.preimage Nat.succ (Function.Injective.injOn Nat.succ_injective)))
          (fun n => sets (n + 1)) := by
    ext pair
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_preimage, prepend]
    constructor
    · intro h
      constructor
      · split_ifs with member
        · exact h 0 member
        · trivial
      · intro n member
        exact h (n + 1) member
    · rintro ⟨head, tail⟩ n member
      cases n with
      | zero => simpa [member] using head
      | succ n => exact tail n member
  rw [boxes, Measure.prod_prod, Measure.infinitePi_pi _ (fun n _ => measurable_sets (n + 1)),
    Finset.prod_preimage' Nat.succ indices _ (fun n => μ (sets n))]
  have remaining : indices.filter (fun n => n ∈ Set.range Nat.succ) = indices.erase 0 := by
    ext n
    cases n <;> simp
  rw [remaining]
  split_ifs with member
  · exact Finset.mul_prod_erase indices (fun n => μ (sets n)) member
  · simp only [measure_univ, one_mul, Finset.erase_eq_of_notMem member]

theorem digitMeasure_eq_sum : digitMeasure =
    Measure.sum (fun digit : Fin 3 => (3 : ℝ≥0∞)⁻¹ • Measure.dirac digit) := by
  apply Measure.ext
  intro set measurable_set
  simp only [digitMeasure, PMF.toMeasure_apply _ measurable_set,
    Measure.sum_apply _ measurable_set, Measure.smul_apply,
    Measure.dirac_apply' _ measurable_set, smul_eq_mul]
  apply tsum_congr
  intro digit
  by_cases member : digit ∈ set <;> simp [member, PMF.uniformOfFintype_apply]

/-- The Bernoulli pushforward satisfies the three-map self-similar measure equation. -/
theorem gasketMeasure_selfSimilar : gasketMeasure =
    Measure.sum (fun digit : Fin 3 => (3 : ℝ≥0∞)⁻¹ •
      gasketMeasure.map (fun point => (1 / 2 : ℝ) • (point + vertex digit))) := by
  have code_measurable := (MoireDimension.continuous_addressPoint vertex).measurable
  have split_law := prepend_law digitMeasure
  change (digitMeasure.prod singleAddressMeasure).map prepend = singleAddressMeasure at split_law
  calc
    gasketMeasure = ((digitMeasure.prod singleAddressMeasure).map prepend).map
        (addressPoint vertex) := by rw [split_law]; rfl
    _ = (digitMeasure.prod singleAddressMeasure).map
        (fun pair => (1 / 2 : ℝ) • (addressPoint vertex pair.2 + vertex pair.1)) := by
      rw [Measure.map_map code_measurable measurable_prepend]
      congr 1
      funext pair
      exact addressPoint_split vertex (prepend pair)
    _ = _ := by
      rw [digitMeasure_eq_sum, Measure.prod_sum_left,
        Measure.map_sum (by fun_prop)]
      congr 1
      funext digit
      rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rw [gasketMeasure, Measure.map_map (by fun_prop) code_measurable]
      rfl

end

end MoireBernoulliRecursion
