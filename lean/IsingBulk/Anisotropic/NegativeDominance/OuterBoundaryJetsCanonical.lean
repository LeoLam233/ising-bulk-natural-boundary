import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsRestricted
import IsingBulk.Anisotropic.NegativeCycles.PhysicalWindingJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeCycles Set Metric MeasureTheory

theorem paperShiftedDensity_eq_weighted (n : ℕ) (lam : ℝ) (zeta A : ℂ→ℂ) (t : ℂ) (v : Fin n→ℝ) :
    paperShiftedDensity n lam zeta A t v=weightedShiftedPhysicalDensity n lam zeta A v t := by
  simp [paperShiftedDensity,weightedShiftedPhysicalDensity,div_eq_mul_inv,
    mul_comm,mul_left_comm,mul_assoc]
  left
  rw [←mul_inv,inv_pow]

theorem weightedShiftedPhysicalDensity_boundary_integral (n : ℕ) (hn : Odd (n+1))
    {lam b : ℝ} {zeta A : ℂ→ℂ} (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im) (j : ℕ) :
    IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j (weightedShiftedPhysicalDensity n lam zeta A v) 0 /
      (j.factorial:ℂ)) (Icc (fun _=>-Real.pi) (fun _=>Real.pi)) ∧
    iteratedDeriv j (fun t=>(A t)^(n+1)*continuedAngularCoefficient n lam (zeta t)) 0 /
      (j.factorial:ℂ) =
      ∫v in Icc (fun _=>-Real.pi) (fun _=>Real.pi),
        iteratedDeriv j (weightedShiftedPhysicalDensity n lam zeta A v) 0/(j.factorial:ℂ) := by
  simpa only [paperShiftedDensity_eq_weighted] using
    paper_weighted_boundary_taylor_integral n hn hzeta hA hS hedge hb hB j

theorem weightedShiftedPhysicalDensity_restricted_jets (n : ℕ) (hn : Odd (n+1))
    {lam b : ℝ} {zeta A : ℂ→ℂ} (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im) :
    ∃r : ℝ,0<r ∧ ∀E : Set (Fin n→ℝ),E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi) →
      AnalyticOnNhd ℂ (fun t=>∫v in E,weightedShiftedPhysicalDensity n lam zeta A v t) (ball 0 r) ∧
      ∀j t,‖t‖<r →
      IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j
        (weightedShiftedPhysicalDensity n lam zeta A v) t/(j.factorial:ℂ)) E ∧
      iteratedDeriv j (fun t=>∫v in E,weightedShiftedPhysicalDensity n lam zeta A v t) t/(j.factorial:ℂ)=
        ∫v in E,iteratedDeriv j (weightedShiftedPhysicalDensity n lam zeta A v) t/(j.factorial:ℂ) := by
  simpa only [paperShiftedDensity_eq_weighted] using
    paper_restricted_boundary_jets n hn hzeta hA hS hedge hb hB

end
end IsingBulk.Anisotropic.NegativeDominance
