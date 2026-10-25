import IsingBulk.Joint.Negative.RestrictedJets
import IsingBulk.Joint.Negative.WindingJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.NegativeCycles Set Metric MeasureTheory

theorem paperShiftedDensity_eq_weighted (n : ℕ) (curve : ℂ→Coupling) (amp : ℂ→ℂ) (t : ℂ) (v : Fin n→ℝ) :
    paperShiftedDensity n curve amp t v=weightedShiftedPhysicalDensity n curve amp v t := by
  simp [paperShiftedDensity,weightedShiftedPhysicalDensity,div_eq_mul_inv,
    mul_comm,mul_left_comm,mul_assoc]
  left
  rw [←mul_inv,inv_pow]

theorem weightedShiftedPhysicalDensity_boundary_integral (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ} (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) (j : ℕ) :
    IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j (weightedShiftedPhysicalDensity n curve amp v) 0 /
      (j.factorial:ℂ)) (Icc (fun _=>-Real.pi) (fun _=>Real.pi)) ∧
    iteratedDeriv j (fun t=>(amp t)^(n+1)*continuedAngularCoefficient n (curve t)) 0 /
      (j.factorial:ℂ) =
      ∫v in Icc (fun _=>-Real.pi) (fun _=>Real.pi),
        iteratedDeriv j (weightedShiftedPhysicalDensity n curve amp v) 0/(j.factorial:ℂ) := by
  simpa only [paperShiftedDensity_eq_weighted] using
    paper_weighted_boundary_taylor_integral n hn hcurve hA hS hedge hb hB j

theorem weightedShiftedPhysicalDensity_restricted_jets (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ} (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) :
    ∃r : ℝ,0<r ∧ ∀E : Set (Fin n→ℝ),E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi) →
      AnalyticOnNhd ℂ (fun t=>∫v in E,weightedShiftedPhysicalDensity n curve amp v t) (ball 0 r) ∧
      ∀j t,‖t‖<r →
      IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j
        (weightedShiftedPhysicalDensity n curve amp v) t/(j.factorial:ℂ)) E ∧
      iteratedDeriv j (fun t=>∫v in E,weightedShiftedPhysicalDensity n curve amp v t) t/(j.factorial:ℂ)=
        ∫v in E,iteratedDeriv j (weightedShiftedPhysicalDensity n curve amp v) t/(j.factorial:ℂ) := by
  simpa only [paperShiftedDensity_eq_weighted] using
    paper_restricted_boundary_jets n hn hcurve hA hS hedge hb hB

end
end IsingBulk.Joint.Negative
