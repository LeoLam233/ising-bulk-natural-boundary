import IsingBulk.Joint.Negative.FamilyDominanceResonantSmall
import IsingBulk.Joint.Negative.FamilyDominanceOuterRanges
import IsingBulk.Anisotropic.NegativeDominance.CoefficientRanges

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem compact_family_complete_coefficient_selected_growth
    (coeff : E→ℕ→ℂ) (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p)
    {a D C : ℝ} (ha : 0<a) (hD : 0<D) {err : ℕ→ℝ}
    (herrto0 : Tendsto err atTop (𝓝 0))
    (hdecomp : ∀ᶠ j : ℕ in atTop,∀ eta ∈ K, HasCoefficientRanges (coeff eta) (familyMember B eta) (familyMember rootB eta) phi p a D C err j) :
    ∃G : ℝ,∃N : ℕ,∀ eta ∈ K, ∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j : ℝ) ∧
      (j : ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j‖/2≤‖coeff eta j‖ ∧
      Real.exp ((j : ℝ)*(2*Real.log (resonantParticle p ell)-G))/2≤‖coeff eta j‖ := by
  classical
  obtain ⟨Nlow,Nsel,hsel⟩ := compact_family_physical_resonant_middle_small B rootB phi hK hB hB0 hroot hroot0 hsq hphi p hp hpOdd (by norm_num : (0 : ℝ)<1/16)
  obtain ⟨Nl,hl⟩ := compact_family_physical_low_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi p ha hD
  obtain ⟨Nh,hh⟩ := compact_family_physical_high_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi p D hD
  obtain ⟨Ne,he⟩ := compact_family_physical_gaussian_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi p D C hD
  obtain ⟨G,Ng,hg⟩ := compact_family_physical_growth_on_crossing_range B rootB phi hK hB hB0 hroot hroot0 hsq hphi p
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hdecomp.and ((herrto0.eventually_lt_const (by norm_num : (0 : ℝ)<1/16)).and
    ((ht.eventually (eventually_ge_atTop (Nlow : ℝ))).and
      ((Real.tendsto_sqrt_atTop.comp ht).eventually (eventually_ge_atTop (1 : ℝ))))))
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,∀ eta ∈ K, ∀ell : ℕ,resonantParticle p ell=n → ∃j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) ∧ (j : ℝ)≤upperCrossingOrder n ∧ n≤j ∧
      ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j‖/2≤‖coeff eta j‖ ∧
      Real.exp ((j : ℝ)*(2*Real.log n-G))/2≤‖coeff eta j‖ := by
    filter_upwards [eventually_ge_atTop Nsel,eventually_ge_atTop Nl,eventually_ge_atTop Nh,
      eventually_ge_atTop Ne,eventually_ge_atTop Ng,eventually_ge_atTop J,
      eventually_selected_mem_middle hp,hexp.eventually_lt_const (by norm_num : (0 : ℝ)<1/16)]
      with n hnsel hnl hnh hne hng hnJ hmem hexp
    intro eta heta ell hell
    have hnodd : Odd n := by rw [←hell]; exact hpOdd.mul ⟨ell,rfl⟩
    obtain ⟨j,hjL,hjH,hnj,hm,hs⟩ := hsel eta heta ell (by simpa only [hell] using hnsel)
    rw [hell] at hjL hjH hnj
    obtain ⟨hd,hη,hlog,hsqrt⟩ := hJ j (hnJ.trans hnj)
    obtain ⟨L,low,mid,high,err,hL,hidentity,hlow,hmid,hhigh,herr⟩ := hd eta heta
    have hk := hmem ell hell j hjL hjH hnj
    let P := ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p (ell+1)) j‖
    have hP : 0≤P := norm_nonneg _
    have hcenter : n+2*p=resonantParticle p (ell+1) := by rw [←hell]; unfold resonantParticle; ring
    have hsother : (∑i∈(resonantMiddleIndices p j).erase (ell+1),‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j‖)≤(1/16 : ℝ)*P := by
      apply hs _ (Finset.notMem_erase _ _)
      · intro i hi; exact middle_indices_gamma_range hsqrt (Finset.mem_of_mem_erase hi)
      · intro i hi
        have hh := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hi)).2.1
        exact_mod_cast (hlog.trans hh.le)
    have hsum : (∑i∈resonantMiddleIndices p j,‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j‖)≤2*P := by
      rw [←Finset.add_sum_erase _ _ hk]
      change P+_≤2*P
      linarith
    have hmid' : ‖mid‖≤P/8 := by
      have hn : 0≤∑i∈resonantMiddleIndices p j,‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
      have h1 := mul_le_mul_of_nonneg_right hη.le hn
      nlinarith only [hmid,h1,hsum]
    have hb : Real.exp (-(n : ℝ))*P≤P/16 := by nlinarith only [mul_le_mul_of_nonneg_right hexp.le hP]
    have hl' : ‖low‖≤P/16 := by
      have h := hl eta heta n hnl hnodd j hjL hjH hnj L hL
      rw [hcenter] at h
      exact hlow.trans (h.trans hb)
    have hh' : ‖high‖≤P/16 := by
      have h := hh eta heta n hnh hnodd j hjL hjH hnj
      rw [hcenter] at h
      exact hhigh.trans (h.trans hb)
    have he' : ‖err‖≤P/16 := by
      have h := he eta heta n hne hnodd j hjL hjH hnj
      rw [hcenter] at h
      exact herr.trans (h.trans hb)
    have htri := complete_coefficient_triangle hk (fun i=>physicalModel (familyMember B eta) (familyMember rootB eta) phi (resonantParticle p i) j) (coeff eta j) low mid high err hidentity
    have hdom : P/2≤‖coeff eta j‖ := by change P≤_ at htri; linarith
    refine ⟨j,hjL,hjH,hnj,hdom,?_⟩
    have hgrow := hg eta heta n hng hnodd j hjL hjH
    rw [hcenter] at hgrow
    have hmain : 0<P := norm_pos_iff.mpr hm
    have heg := Real.exp_le_exp.mpr hgrow
    rw [Real.exp_log hmain] at heg
    linarith only [heg,hdom]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  exact ⟨G,N,fun eta heta ell hell => hN _ hell eta heta ell rfl⟩


end
end IsingBulk.Joint.Negative
