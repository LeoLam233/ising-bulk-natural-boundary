import IsingBulk.Anisotropic.NegativeDominance.GapComposedCauchy
import IsingBulk.Anisotropic.NegativeDominance.NonresonantBoundaryGap

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- The actual complete outer integrand, including its lattice denominator,
has uniform Cauchy jets on the genuine paper-coordinate particle scale. -/
theorem outer_composed_fullIntegrand_cauchy {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      σ≤∑i,(q i)^2 → ∀j : ℕ,∀u : ℂ,‖u‖<a/(N : ℝ) →
      ‖iteratedDeriv j (fun w=>edgeFullIntegrand b B S (f w) q) u‖≤
        (j.factorial : ℝ)*(K*particleEdgeMajorant r C M N)/(a/(N : ℝ))^j := by
  obtain ⟨κ,hκ,hgap⟩ := outer_boundary_product_gap hb hB σ hσ
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hjets⟩ :=
    composed_fullIntegrand_cauchy_of_boundary_gap hb hB hBa hSa hS0 hf hf0 κ hκ
  refine ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,?_⟩
  intro N hN q hq hS j u hu
  exact hjets N hN q hq (by simpa only [edgeRootProduct,edgeParamRoot_zero] using hgap N q hq hS) j u hu

/-- All nonresonant particle orders, on the full angular cube, satisfy the
same a/N Cauchy bound. The primitive phase gap is proved, not assumed. -/
theorem prime_nonresonant_composed_fullIntegrand_cauchy {B S f : ℂ→ℂ} {p k : ℕ}
    (hp : p.Prime) (hk : 0<k) (hkp : 2*k<p)
    (hb : |Real.cos (primePhase p k)|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀N : ℕ,1≤N → ¬p∣N → ∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      ∀j : ℕ,∀u : ℂ,‖u‖<a/(N : ℝ) →
      ‖iteratedDeriv j (fun w=>edgeFullIntegrand (Real.cos (primePhase p k)) B S (f w) q) u‖≤
        (j.factorial : ℝ)*(K*particleEdgeMajorant r C M N)/(a/(N : ℝ))^j := by
  obtain ⟨κ,hκ,hgap⟩ := prime_negative_boundary_product_gap hp hk hkp hb hB
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hjets⟩ :=
    composed_fullIntegrand_cauchy_of_boundary_gap hb hB hBa hSa hS0 hf hf0 κ hκ
  refine ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,?_⟩
  intro N hN hres q hq j u hu
  exact hjets N hN q hq (by simpa only [edgeRootProduct,edgeParamRoot_zero] using hgap N hres q hq) j u hu

end
end IsingBulk.Anisotropic.NegativeDominance
