import IsingBulk.Anisotropic.NegativeDominance.ResonantMiddleSum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology BigOperators

theorem middle_geometric_ratio_tendsto_zero {p : ℕ} (hp : 0<p) :
    Tendsto (fun j : ℕ => 2*(Real.exp (-((p : ℝ)^2/2*Real.log j))/
      (1-Real.exp (-((p : ℝ)^2/2*Real.log j))))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have ha := (tendsto_const_mul_atBot_of_neg (show -((p : ℝ)^2/2)<0 by nlinarith [sq_pos_of_pos hpR])).mpr hlog
  have he : Tendsto (fun j : ℕ => Real.exp (-((p : ℝ)^2/2*Real.log j))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_atBot.comp ha
  have hh := (he.div (tendsto_const_nhds.sub he) (by norm_num : (1 : ℝ)-0≠0)).const_mul 2
  simpa only [sub_zero,zero_div,mul_zero,Pi.div_apply] using hh

/-- Every competing resonant middle index has an arbitrarily small total
norm compared with the single selected index, at one common integer order. -/
theorem physical_resonant_middle_small
    (B rootB : ℂ→ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),rootB t^2=B t) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p) {ε : ℝ} (hε : 0<ε) :
    ∃Nlow N : ℕ,∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j : ℝ) ∧
      (j : ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      physicalModel B rootB phi (resonantParticle p (ell+1)) j≠0 ∧
      ∀I : Finset ℕ,ell+1∉I →
      (∀i∈I,2*alpha (resonantParticle p i)≤j) →
      (∀i∈I,Nlow≤resonantParticle p i) →
      (∑i∈I,‖physicalModel B rootB phi (resonantParticle p i) j‖)≤
        ε*‖physicalModel B rootB phi (resonantParticle p (ell+1)) j‖ := by
  obtain ⟨Nlow,N,hsel⟩ := physical_resonant_middle_sum B rootB phi hB hB0 hroot hroot0 hsq hphi p hp hpOdd
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((middle_geometric_ratio_tendsto_zero hp).eventually_lt_const hε)
  refine ⟨Nlow,max N J,fun ell hell => ?_⟩
  obtain ⟨j,hjL,hjH,hnj,hm,hs⟩ := hsel ell (le_trans (le_max_left _ _) hell)
  refine ⟨j,hjL,hjH,hnj,hm,fun I hI hIA hIlow => ?_⟩
  have hh := hJ j ((le_max_right _ _).trans (hell.trans hnj))
  have hsum := hs I hI hIA hIlow
  have hmul := mul_le_mul_of_nonneg_right hh.le (norm_nonneg (physicalModel B rootB phi (resonantParticle p (ell+1)) j))
  nlinarith only [hsum,hmul]

end
end IsingBulk.Anisotropic.NegativeDominance
