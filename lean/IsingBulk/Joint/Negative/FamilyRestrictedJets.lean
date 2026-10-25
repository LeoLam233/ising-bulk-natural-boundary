import IsingBulk.Joint.Negative.FamilyBoundaryIdentity
import IsingBulk.Joint.Negative.JetPartition
import IsingBulk.Anisotropic.NegativeDominance.PhysicalRestrictedPeriod

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Anisotropic.NegativeCycles IsingBulk.Joint.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- The exact shifted-density identity also holds on every measurable restricted
angular region. This is not inferred from a whole-period equality. -/
theorem physical_negative_restricted_boundary_jet_integral (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (hS : S (curve 0)≠0)
    (he : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im)
    {D : Set (Fin n→ℝ)} (hD : MeasurableSet D)
    (hsub : D⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi)) :
    (∫v in D,physicalDensityTaylor n curve amp j v)=
      ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
        ∫v in D, iteratedDeriv j
          (fun t => independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
            (negativeShiftedAngles n v)) 0/(j.factorial:ℂ)
            ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  have hd (v : Fin n→ℝ) : physicalDensityTaylor n curve amp j v=
      (((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n)*(-1:ℂ)^((n+1).choose 2)*
        (iteratedDeriv j
          (fun t => independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
            (negativeShiftedAngles n v)) 0/(j.factorial:ℂ)) := by
    have hg : weightedShiftedPhysicalDensity n curve amp v=
        (fun t=>paperShiftedDensity n curve amp t v) := by
      funext t
      exact (paperShiftedDensity_eq_weighted n curve amp t v).symm
    rw [physicalDensityTaylor,hg,
      (paperShiftedDensity_independent_germ n hn hc hS he hb hB v).iteratedDeriv_eq j,
      iteratedDeriv_const_mul_field]
    ring
  simp_rw [hd]
  rw [integral_const_mul,edgeAngleMeasure_restricted_integral_eq n hD hsub]
  ring

/-- A true complete-integrand Cauchy estimate implies the corresponding actual
restricted physical Taylor estimate, with the exact probability normalization. -/
theorem physical_restricted_boundary_jet_bound (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (hS : S (curve 0)≠0)
    (he : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im)
    {D : Set (Fin n→ℝ)} (hD : MeasurableSet D)
    (hsub : D⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi))
    {M : ℝ} (hM : 0≤M)
    (hbound : ∀v∈D, ‖iteratedDeriv j
      (fun t=>independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
        (negativeShiftedAngles n v)) 0‖≤(j.factorial:ℝ)*M) :
    ‖∫v in D,physicalDensityTaylor n curve amp j v‖≤M := by
  rw [physical_negative_restricted_boundary_jet_integral n j hn hc hS he hb hB hD hsub,
    norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hfac : ‖(((n+1).factorial:ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  apply (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
  have hi := norm_integral_le_of_norm_le
    (f := fun v : Fin n→ℝ => iteratedDeriv j
      (fun t=>independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
        (negativeShiftedAngles n v)) 0/(j.factorial:ℂ))
    (integrable_const M : Integrable (fun _q : Fin n→ℝ=>M)
      ((Measure.pi (fun _=>edgeAngleMeasure)).restrict D)) (by
    filter_upwards [ae_restrict_mem hD] with v hv
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j : 0<(j.factorial:ℝ))).mpr
      (by simpa only [mul_comm] using hbound v hv))
  apply hi.trans
  simp only [integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ]
  exact mul_le_of_le_one_left hM measureReal_le_one

end
end IsingBulk.Joint.Negative
