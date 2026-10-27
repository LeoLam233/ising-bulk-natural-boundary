import IsingBulk.Preferred22.BoxIntegration
import Mathlib.MeasureTheory.Group.LIntegral

/-! Exact translation of the remaining angular variables to their branch
coordinates, retaining product Lebesgue measure and every diameter. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

def preferredShiftedOneBodyBox (n : ℕ) (b t r : ℝ) : Set (Fin n → ℝ) :=
  (fun z : Fin n → ℝ => fun i => z i+b) ⁻¹' preferredOneBodyBox n t r

theorem preferredOneBodyBox_measurable (n : ℕ) (t r : ℝ) :
    MeasurableSet (preferredOneBodyBox n t r) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem preferredShiftedOneBodyBox_measurable (n : ℕ) (b t r : ℝ) :
    MeasurableSet (preferredShiftedOneBodyBox n b t r) :=
  (preferredOneBodyBox_measurable n t r).preimage (by fun_prop)

theorem preferredShiftedOneBodyBox_mem {n : ℕ} {b t r : ℝ} {z : Fin n → ℝ} :
    z ∈ preferredShiftedOneBodyBox n b t r ↔ ∀ i, t-2*r ≤ z i+b ∧ z i+b ≤ t+2*r := by
  simp only [preferredShiftedOneBodyBox,preferredOneBodyBox,Set.mem_preimage,Set.mem_univ_pi,Set.mem_Icc]

/-- The actual remaining angular variables are translated to u=theta+b
with exactly unit measure, before applying the proved q22 product bound. -/
theorem preferredShiftedOneBodyBox_lintegral (n : ℕ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (b t : ℝ) :
    (∫⁻ z in preferredShiftedOneBodyBox n b t r,
      ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+b))) ≤
      ENNReal.ofReal ((32*r/Real.sqrt (|t|+r+ε))^n) := by
  have hs := lintegral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
    ((preferredOneBodyBox n t r).indicator
      (fun x : Fin n → ℝ => ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (x i))))
    (fun _ : Fin n => b)
  have he : (fun z : Fin n → ℝ => (preferredOneBodyBox n t r).indicator
      (fun x => ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (x i))) (z+(fun _ => b))) =
      (preferredShiftedOneBodyBox n b t r).indicator
        (fun z => ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+b))) := by
    funext z
    rfl
  rw [he,lintegral_indicator (preferredShiftedOneBodyBox_measurable n b t r),
    lintegral_indicator (preferredOneBodyBox_measurable n t r)] at hs
  rw [hs,← ofReal_integral_eq_lintegral_ofReal (preferredOneBodyBox_integrable n hε hr t)
    (Filter.Eventually.of_forall (fun x : Fin n → ℝ => Finset.prod_nonneg
      (fun i _ => preferredOneBodyMajorant_nonneg)))]
  exact ENNReal.ofReal_le_ofReal (preferredOneBodyBox_bound n hε hr t)

end
end IsingBulk.Preferred22
