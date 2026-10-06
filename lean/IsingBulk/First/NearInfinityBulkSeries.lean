import IsingBulk.First.FarExteriorFormFactor
import IsingBulk.First.BulkSymmetry
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Ordinary normal convergence of the actual bulk expansion near infinity.
The summable majorant applies at a fixed small radius, away from the unit circle. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology BigOperators

def quarterEvenMajorant (n : ℕ) : ℝ := 8*(1/4:ℝ)^(2*(n+1))

theorem quarterEvenMajorant_summable : Summable quarterEvenMajorant := by
  have hg : Summable (fun n : ℕ => 8*(1/4:ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)).mul_left 8
  exact hg.comp_injective (fun a b h => by omega)

theorem quarterEvenFormFactor_norm_le (n : ℕ) {s : ℂ} (hs : 16 < ‖s‖) :
    ‖doubleFormFactor (2*(n+1)) (1/4) s‖ ≤ quarterEvenMajorant n :=
  farExterior_doubleFormFactor_quarter_norm_bound _ (by omega) hs

theorem quarterEvenFormFactor_summable {s : ℂ} (hs : 16 < ‖s‖) :
    Summable (fun n : ℕ => doubleFormFactor (2*(n+1)) (1/4) s) :=
  quarterEvenMajorant_summable.of_norm_bounded (fun n => quarterEvenFormFactor_norm_le n hs)

theorem quarterEvenFormFactor_summable_norm {s : ℂ} (hs : 16 < ‖s‖) :
    Summable (fun n : ℕ => ‖doubleFormFactor (2*(n+1)) (1/4) s‖) := by
  apply quarterEvenMajorant_summable.of_norm_bounded
  intro n
  simpa only [norm_norm] using quarterEvenFormFactor_norm_le n hs

theorem magnetizationSquared_analyticOn_exterior :
    AnalyticOnNhd ℂ magnetizationSquared {s : ℂ | 1 < ‖s‖} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_norm)
  intro s hs
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by change 1 < ‖s‖ at hs; linarith)
  have hi : DifferentiableAt ℂ (fun t : ℂ => (t^(4:ℕ))⁻¹) s :=
    (differentiableAt_id.pow 4).inv (pow_ne_zero 4 hs0)
  exact ((differentiableAt_const (1:ℂ)).sub hi |>.cpow_const
    (magnetization_argument_slit hs)).differentiableWithinAt

theorem normalizedBulkSeries_quarter_analyticOn :
    AnalyticOnNhd ℂ (normalizedBulkSeries (1/4)) {s : ℂ | 16 < ‖s‖} := by
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => ∑' n : ℕ, doubleFormFactor (2*(n+1)) (1/4) s)
      {s : ℂ | 16 < ‖s‖} := by
    apply Complex.differentiableOn_tsum_of_summable_norm quarterEvenMajorant_summable
    · intro n
      exact (doubleFormFactor_quarter_analyticOn _ (by omega)).differentiableOn
    · exact isOpen_lt continuous_const continuous_norm
    · intro n s hs
      exact quarterEvenFormFactor_norm_le n hs
  have hm : DifferentiableOn ℂ magnetizationSquared {s : ℂ | 16 < ‖s‖} :=
    magnetizationSquared_analyticOn_exterior.differentiableOn.mono (by
      intro s hs; change 16 < ‖s‖ at hs; change 1 < ‖s‖; linarith)
  have hfull := ((differentiableOn_const (c := (1:ℂ))).sub hm).add
    (((differentiableOn_const (c := (2:ℂ))).mul hm).mul hsum)
  exact hfull.analyticOnNhd (isOpen_lt continuous_const continuous_norm)

end
end IsingBulk.First
