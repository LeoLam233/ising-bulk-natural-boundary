import IsingBulk.Anisotropic.NegativeDominance.OuterNonresonantJets
import IsingBulk.Anisotropic.NegativeDominance.NegativeIntegratedJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter
open scoped BigOperators

/-- The actual normalized outer integral of manuscript-coordinate Taylor
jets. No derivative-of-integral exchange is assumed in this estimate. -/
theorem outer_negative_integral_cauchy {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀n j : ℕ,∀E : Set (Fin n→ℝ),MeasurableSet E →
      (∀q∈E,σ≤∑i,(negativeShiftedAngles n q i)^2) →
      ∀χ : (Fin n→ℝ)→ℂ,(∀q∈E,‖χ q‖≤1) → ∀u : ℂ,‖u‖<a/((n+1 : ℕ) : ℝ) →
      ‖∫q in E,χ q*(iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u/
        (j.factorial : ℂ)) ∂Measure.pi (fun _=>edgeAngleMeasure)‖≤
        K*particleEdgeMajorant r C M (n+1)*(((n+1 : ℕ) : ℝ)/a)^j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hjets⟩ := outer_composed_fullIntegrand_cauchy hb hB hBa hSa hS0 hf hf0 σ hσ
  refine ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,?_⟩
  intro n j E hE houter χ hχ u hu
  let D := K*particleEdgeMajorant r C M (n+1)*(((n+1 : ℕ) : ℝ)/a)^j
  have hD : 0≤D := by
    exact mul_nonneg (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity)
  have hfac : (0 : ℝ)<j.factorial := by positivity
  have hpoint (q : Fin n→ℝ) (hq : q∈E) :
      ‖χ q*(iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u/(j.factorial : ℂ))‖≤D := by
    have hj := hjets (n+1) (by omega) (negativeShiftedAngles n q) (fun _=>wrapAngle_mem _) (houter q hq) j u hu
    have hjdiv := div_le_div_of_nonneg_right hj hfac.le
    have he : ((j.factorial : ℝ)*(K*particleEdgeMajorant r C M (n+1))/(a/((n+1 : ℕ) : ℝ))^j)/(j.factorial : ℝ)=D := by
      dsimp [D]
      rw [div_pow,div_pow]
      field_simp
    rw [he] at hjdiv
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hχ q hq)).trans
    simpa only [negativeShiftedFullIntegrand,norm_div,Complex.norm_natCast] using hjdiv
  rw [←integral_indicator hE]
  have hh := norm_integral_le_of_norm_le
    (f := E.indicator (fun q=>χ q*(iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u/(j.factorial : ℂ))))
    (integrable_const D :
      Integrable (fun _q : Fin n→ℝ=>D) (Measure.pi (fun _=>edgeAngleMeasure)))
    (Eventually.of_forall (fun q=>by
      by_cases hq : q∈E
      · simpa only [indicator_of_mem hq] using hpoint q hq
      · simpa only [indicator_of_notMem hq,norm_zero] using hD))
  simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
