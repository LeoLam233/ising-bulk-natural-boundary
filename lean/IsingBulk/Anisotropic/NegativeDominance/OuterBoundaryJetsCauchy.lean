import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsActual
import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

def outerNegativePeriod (b : ℝ) (B S : ℂ→ℂ) (n : ℕ)
    (E : Set (Fin n→ℝ)) (χ : (Fin n→ℝ)→ℂ) (u : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
    ∫q in E,χ q*negativeShiftedFullIntegrand b B S n u q
      ∂Measure.pi (fun _=>edgeAngleMeasure)

/-- Cauchy bounds for derivatives of the actual outer integral, rather than
merely bounds for integrals of derivatives. -/
theorem outer_negative_actual_jet_cauchy {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀n j : ℕ,∀E : Set (Fin n→ℝ),MeasurableSet E →
      (∀q∈E,σ≤∑i,(negativeShiftedAngles n q i)^2) →
      ∀χ : (Fin n→ℝ)→ℂ,Continuous χ → (∀q∈E,‖χ q‖≤1) →
      ∀u : ℂ,‖u‖<a/((n+1:ℕ):ℝ) →
      iteratedDeriv j (fun w=>outerNegativePeriod b B S n E χ (f w)) u=
        ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
        ∫q in E,χ q*iteratedDeriv j
          (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u
          ∂Measure.pi (fun _=>edgeAngleMeasure) ∧
      ‖iteratedDeriv j (fun w=>outerNegativePeriod b B S n E χ (f w)) u /
        (j.factorial:ℂ)‖≤K*particleEdgeMajorant r C M (n+1)*(((n+1:ℕ):ℝ)/a)^j := by
  obtain ⟨a,ha,hjets⟩ := outer_negative_integral_analytic_jets hb hB hBa hSa hS0 hf hf0 σ hσ
  obtain ⟨a',r,C,M,K,ha',hr,hr1,hC,hM,hK,hbound⟩ :=
    outer_negative_integral_cauchy hb hB hBa hSa hS0 hf hf0 σ hσ
  refine ⟨min a a',r,C,M,K,lt_min ha ha',hr,hr1,hC,hM,hK,?_⟩
  intro n j E hE houter χ hχ hχb u hu
  have hN : (0:ℝ)<(n+1:ℕ) := by positivity
  have hua := hu.trans_le (div_le_div_of_nonneg_right (min_le_left a a') hN.le)
  have hua' := hu.trans_le (div_le_div_of_nonneg_right (min_le_right a a') hN.le)
  have heq : iteratedDeriv j (fun w=>outerNegativePeriod b B S n E χ (f w)) u=
      ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
      ∫q in E,χ q*iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u
        ∂Measure.pi (fun _=>edgeAngleMeasure) := by
    unfold outerNegativePeriod
    rw [iteratedDeriv_const_mul_field,(hjets n E hE houter χ hχ).2 j u hua |>.2]
  refine ⟨heq,?_⟩
  rw [heq,mul_div_assoc,←integral_div]
  have he : (fun q : Fin n→ℝ=>χ q*iteratedDeriv j
      (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u/(j.factorial:ℂ))=
      (fun q=>χ q*(iteratedDeriv j
      (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u/(j.factorial:ℂ))) := by
    funext q; ring
  rw [he,norm_mul]
  have hfac : ‖((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)‖≤1 := by
    simp only [norm_mul,norm_inv,Complex.norm_natCast,norm_pow,norm_neg,norm_one,one_pow,mul_one]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  apply (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
  apply (hbound n j E hE houter χ hχb u hua').trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _))
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_left hN.le (lt_min ha ha') (min_le_right _ _)

end
end IsingBulk.Anisotropic.NegativeDominance
