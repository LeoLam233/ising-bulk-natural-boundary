import IsingBulk.Joint.Negative.FamilyDominanceRangeGrowth
import IsingBulk.Anisotropic.NegativeDominance.GaussianRemainderDominance

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_physical_high_on_crossing_range
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (q : ℕ) (D : ℝ) (hD : 0<D) :
    ∃N : ℕ,∀ eta ∈ K, ∀n≥N,Odd n → ∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      D*Real.exp ((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32)≤
        Real.exp (-(n : ℝ))*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖ := by
  obtain ⟨M,Ng,hg⟩ := compact_family_physical_growth_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi q
  obtain ⟨Nh,hh⟩ := eventually_atTop.mp (high_envelope_vs_growth D M hD)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_crossing_scale (|M|+1) (max Ng (max Nh 1)))
  refine ⟨N,?_⟩
  intro eta heta n hn ho j hjL hjH hnj
  obtain ⟨hnb,hlog,_hu⟩ := hN n hn
  have hnG : Ng≤n := (le_max_left _ _).trans hnb
  have hnH : Nh≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnb)
  have hgrowth := hg eta heta n hnG ho j hjL hjH
  have hrate : 0<2*Real.log (n : ℝ)-M := by linarith [le_abs_self M,abs_nonneg M]
  have hjpos : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hP : 0<‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖ := by
    by_contra h
    have he := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [he,Real.log_zero] at hgrowth
    exact (not_le_of_gt (mul_pos hjpos hrate)) hgrowth
  exact hh n hnH j hnj hjH _ hP hgrowth


theorem compact_family_physical_gaussian_on_crossing_range
    (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (q : ℕ) (D C : ℝ) (hD : 0<D) :
    ∃N : ℕ,∀ eta ∈ K, ∀n≥N,Odd n → ∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+C*((j : ℝ)+1))≤
        Real.exp (-(n : ℝ))*‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (n+2*q) j‖ := by
  obtain ⟨N,hN⟩ := compact_family_physical_high_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi q D hD
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (eventually_gaussian_moment_le_high C)
  refine ⟨max N J,fun eta heta n hn ho j hjL hjH hnj => ?_⟩
  apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hJ j (by omega))) hD.le)
  exact hN eta heta n (by omega) ho j hjL hjH hnj


end
end IsingBulk.Joint.Negative
