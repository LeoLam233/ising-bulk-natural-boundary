import IsingBulk.Anisotropic.NegativeDominance.PhysicalGrowth
import IsingBulk.Anisotropic.NegativeDominance.LogarithmicLowRange

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The growing low-particle Cauchy envelope is negligible on the genuine
integer model selection. This compares the already derived envelope to the
exact model, without presupposing any physical middle-range approximation. -/
theorem physical_selected_low_dominance
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2=B t) (hphi : Real.sin phi≠0)
    (q : ℕ) (hq : 0<q) {a D : ℝ} (ha : 0<a) (hD : 0<D) :
    ∃ N : ℕ, ∀ n≥N, Odd n → ∃ j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) ∧ (j : ℝ)≤upperCrossingOrder n ∧ n≤j ∧
      ∀ L : ℕ, (L : ℝ)≤Real.log j →
        D*(L : ℝ)^3*((L : ℝ)^3/a)^j ≤
          Real.exp (-(n : ℝ))*‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨K,Ng,hg⟩ := physical_selected_model_growth B rootB phi hB hB0 hroot hroot0 hsq hphi q hq
  obtain ⟨Nl,hl⟩ := eventually_atTop.mp (logarithmic_low_envelope_vs_growth ha hD K)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_crossing_scale (|K|+1) (max Ng (max Nl 1)))
  refine ⟨N,?_⟩
  intro n hn ho
  obtain ⟨hnb,hlog,hu⟩ := hN n hn
  have hnG : Ng≤n := (le_max_left _ _).trans hnb
  have hnL : Nl≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnb)
  obtain ⟨j,hjL,hjH,hnj,hgrowth⟩ := hg n hnG ho
  have hjH' : j≤n^3 := by
    have h := mul_le_mul_of_nonneg_left hu (sq_nonneg (n : ℝ))
    dsimp [upperCrossingOrder] at hjH
    exact_mod_cast (show (j : ℝ)≤(n : ℝ)^3 by nlinarith only [h,hjH])
  have hrate : 0<2*Real.log (n : ℝ)-K := by linarith [le_abs_self K,abs_nonneg K]
  have hjpos : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hP : 0<‖physicalModel B rootB phi (n+2*q) j‖ := by
    by_contra hh
    have he := le_antisymm (not_lt.mp hh) (norm_nonneg _)
    rw [he,Real.log_zero] at hgrowth
    exact (not_le_of_gt (mul_pos hjpos hrate)) hgrowth
  refine ⟨j,hjL,hjH,hnj,?_⟩
  intro L hL
  exact hl n hnL j hnj hjH' L hL _ hP hgrowth

end
end IsingBulk.Anisotropic.NegativeDominance
