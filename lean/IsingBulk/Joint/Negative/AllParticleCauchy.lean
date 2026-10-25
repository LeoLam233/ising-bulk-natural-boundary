import IsingBulk.Joint.Negative.ComposedJets
import IsingBulk.Anisotropic.NegativeDominance.AllParticleBoundaryCauchy
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.RegularEdges Set Filter MeasureTheory
open scoped Topology

/-- Actual all-particle boundary Cauchy bounds in the manuscript coordinate.
Every constant precedes both the derivative order and particle index. -/
theorem scaled_negative_boundary_cauchy_all_particles
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {b : ℝ} {B S amp f : ℂ→ℂ} {curve : ℂ→Coupling} {U V : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ amp 0) (hA0 : amp 0≠0)
    (hcurve : AnalyticAt ℂ curve 0)
    (hSedge : IsingBulk.Joint.S (curve 0)≠0)
    (hedge : IsingBulk.Joint.A (curve 0)+T (curve 0)=(b : ℂ)*IsingBulk.Joint.S (curve 0))
    (hBedge : 0<(-T (curve 0)/IsingBulk.Joint.S (curve 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ curve U) (hAa : AnalyticOnNhd ℂ amp U)
    (hz : ∀ u∈U, curve u∉spectralSet)
    (hS0 : ∀ u∈U, IsingBulk.Joint.S (curve u)≠0)
    (hB : ∀ u∈U, B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : ∀ u∈U, S u=IsingBulk.Joint.S (curve u))
    (he : ∀ u∈U, transferC (curve u)+transferB (curve u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hf0 : AnalyticAt ℂ f 0) (hfz : f 0=0) (hmap : MapsTo f V U)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈V) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ (j n : ℕ), Odd (n+1) →
        ‖iteratedDeriv j (fun t => (amp (f t))^(n+1)*continuedAngularCoefficient n (curve (f t))) 0‖≤
          (j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/((n+1 : ℕ) : ℝ)^3)^j := by
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hbound⟩ :=
    odd_negative_composed_integrand_cauchy_jets (S := fun v => S v/amp v) hb hB0 hBa
      (hSa.div hAa0 hA0) (div_ne_zero hSzero hA0) hf0 hfz
  refine ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,?_⟩
  intro j n hn
  have hG : AnalyticAt ℂ (fun t => (amp (f t))^(n+1)*continuedAngularCoefficient n (curve (f t))) 0 :=
    (weighted_coefficient_negative_analyticAt n hn hcurve hAa0 hSedge hedge hb hBedge).comp_of_eq hf0 hfz
  have hc : ContinuousAt (iteratedDeriv j (fun t => (amp (f t))^(n+1)*continuedAngularCoefficient n (curve (f t)))) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (hG.iterated_deriv j).continuousAt
  have hlim : Tendsto (fun t => iteratedDeriv j
      (fun w => negativeShiftedPeriod b B (fun v => S v/amp v) n (f w)) (path t)) l
      (𝓝 (iteratedDeriv j (fun t => (amp (f t))^(n+1)*continuedAngularCoefficient n (curve (f t))) 0)) := by
    apply (hc.tendsto.comp hp).congr'
    filter_upwards [hin] with t ht
    have hevent : (fun w => negativeShiftedPeriod b B (fun v => S v/amp v) n (f w)) =ᶠ[𝓝 (path t)]
        (fun t => (amp (f t))^(n+1)*continuedAngularCoefficient n (curve (f t))) := by
      filter_upwards [hV.mem_nhds ht] with w hw
      rw [negativeShiftedPeriod_div_scale,
        ←continuedAngularCoefficient_eq_negativeShiftedPeriod n (hB _ (hmap hw)) (hS _ (hmap hw))
          (he _ (hmap hw)) (hup _ (hmap hw)) (hBi _ (hmap hw))]
    exact (hevent.iteratedDeriv_eq j).symm
  apply le_of_tendsto hlim.norm
  have hsmall : ∀ᶠ t in l, ‖path t‖<a/((n+1 : ℕ) : ℝ)^3 :=
    hp.norm.eventually (gt_mem_nhds (by simp only [norm_zero]; positivity))
  filter_upwards [hin,hsmall] with t ht hsmall
  rw [scaledNegativeShiftedPeriod_comp_iteratedDeriv n j hU ha hAa hz hS0 hB hS he hup hBi hV hf hmap ht,
    norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hfac : ‖(((n+1).factorial : ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  apply (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
  have hi := norm_integral_le_of_norm_le
    (integrable_const ((j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
      (a/((n+1 : ℕ) : ℝ)^3)^j) : Integrable (fun _q : Fin n → ℝ => _)
        (Measure.pi (fun _ => edgeAngleMeasure)))
    (Filter.Eventually.of_forall (fun q : Fin n → ℝ => hbound j n hn q (path t) hsmall))
  simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hi

end
end IsingBulk.Joint.Negative
