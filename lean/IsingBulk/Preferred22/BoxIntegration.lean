import IsingBulk.Preferred22.OneBodyScale
import Mathlib.MeasureTheory.Integral.Pi

/-! Repeated literal one-body integration on the fixed-mean window used
for the all-diameter right-shell estimate. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

def preferredOneBodyBox (k : ℕ) (t r : ℝ) : Set (Fin k → ℝ) :=
  Set.univ.pi (fun _ => Icc (t-2*r) (t+2*r))

theorem preferredOneBodyBox_integrable (k : ℕ) {ε r : ℝ} (hε : 0 < ε) (_hr : 0 < r)
    (t : ℝ) :
    IntegrableOn (fun x : Fin k → ℝ => ∏ i, preferredOneBodyMajorant ε (x i))
      (preferredOneBodyBox k t r) := by
  have h1 : IntegrableOn (preferredOneBodyMajorant ε) (Icc (t-2*r) (t+2*r)) :=
    (preferredOneBodyMajorant_continuous hε).continuousOn.integrableOn_Icc
  have hp := Integrable.fintype_prod (fun _i : Fin k => h1)
  change Integrable _ ((volume : Measure (Fin k → ℝ)).restrict (preferredOneBodyBox k t r))
  rw [preferredOneBodyBox,volume_pi,Measure.restrict_pi_pi]
  exact hp

/-- The full product integral is evaluated before applying the source q22
bound; all coordinates and all small diameters are retained. -/
theorem preferredOneBodyBox_integral (k : ℕ) {ε r : ℝ} (_hε : 0 < ε) (hr : 0 < r)
    (t : ℝ) :
    (∫ x in preferredOneBodyBox k t r, ∏ i, preferredOneBodyMajorant ε (x i)) =
      (∫ u : ℝ in (t-2*r)..(t+2*r), preferredOneBodyMajorant ε u)^k := by
  rw [preferredOneBodyBox,volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_pow,Fintype.card_fin]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith : t-2*r ≤ t+2*r),
    integral_Icc_eq_integral_Ioc]

/-- The independent remaining-coordinate integrations in q28 cost exactly
one r/sqrt(T) factor per remaining coordinate. -/
theorem preferredOneBodyBox_bound (k : ℕ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (t : ℝ) :
    (∫ x in preferredOneBodyBox k t r, ∏ i, preferredOneBodyMajorant ε (x i)) ≤
      (32*r/Real.sqrt (|t|+r+ε))^k := by
  rw [preferredOneBodyBox_integral k hε hr t]
  apply pow_le_pow_left₀
  · exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => preferredOneBodyMajorant_nonneg)
  · exact preferred_oneBody_mean_scale hε hr t

end
end IsingBulk.Preferred22
