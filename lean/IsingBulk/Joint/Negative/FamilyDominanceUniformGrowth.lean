import IsingBulk.Joint.Negative.FamilyDominanceRadius

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

/-- Every common geometric coefficient bound fails beyond one common particle threshold.
The selected derivative order may vary with the parameter. -/
theorem compact_family_complete_coefficient_uniform_unbounded
    (coeff : E→ℕ→ℂ) (B rootB : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta)≠0)
    (hroot : ∀ eta ∈ K, AnalyticAt ℂ rootB (0,eta)) (hroot0 : ∀ eta ∈ K, rootB (0,eta)≠0)
    (hsq : ∀ eta ∈ K, ∀ᶠ t : ℂ in 𝓝 0, rootB (t,eta)^2=B (t,eta)) (hphi : Real.sin phi≠0)
    (p : ℕ) (hp : 0<p) (hpOdd : Odd p)
    {a D C : ℝ} (ha : 0<a) (hD : 0<D) {err : ℕ→ℝ}
    (herrto0 : Tendsto err atTop (𝓝 0))
    (hdecomp : ∀ᶠ j : ℕ in atTop,∀ eta ∈ K, HasCoefficientRanges (coeff eta) (familyMember B eta) (familyMember rootB eta) phi p a D C err j) :
    ∀ r : ℝ, 0<r → ∀ Cbound : ℝ, ∃ N : ℕ, ∀ eta ∈ K,
      ∀ ell : ℕ, N≤resonantParticle p ell → ∃ j : ℕ,
        lowerCrossingOrder (resonantParticle p ell)-1<(j:ℝ) ∧
        (j:ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
        Cbound<‖coeff eta j‖*r^j := by
  obtain ⟨G,N,hsel⟩ := compact_family_complete_coefficient_selected_growth coeff B rootB phi hK
    hB hB0 hroot hroot0 hsq hphi p hp hpOdd ha hD herrto0 hdecomp
  intro r hr Cbound
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlog,hNlog⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop ((G-Real.log r+1)/2)))
  obtain ⟨Nc,hNc⟩ := exists_nat_gt (2*Cbound)
  refine ⟨max N (max Nlog Nc),?_⟩
  intro eta heta ell hell
  let n := resonantParticle p ell
  have hnN : N≤n := (le_max_left _ _).trans hell
  have hnlog : Nlog≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hell)
  have hnC : Nc≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hell)
  obtain ⟨j,hjL,hjH,hnj,_hdom,hbound⟩ := hsel eta heta ell hnN
  refine ⟨j,hjL,hjH,hnj,?_⟩
  have hrate : 1≤2*Real.log (n:ℝ)-G+Real.log r := by linarith [hNlog n hnlog]
  have hmul := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg j : (0:ℝ)≤j)
  have hpow : r^j=Real.exp ((j:ℝ)*Real.log r) := by rw [Real.exp_nat_mul,Real.exp_log hr]
  have hcombine : Real.exp ((j:ℝ)*(2*Real.log (n:ℝ)-G))/2*r^j=
      Real.exp ((j:ℝ)*(2*Real.log (n:ℝ)-G+Real.log r))/2 := by
    rw [hpow,div_mul_eq_mul_div,←Real.exp_add]
    congr 1
    congr 1
    ring
  have hscaled : Real.exp (j:ℝ)/2≤‖coeff eta j‖*r^j := by
    calc
      _ ≤ Real.exp ((j:ℝ)*(2*Real.log (n:ℝ)-G+Real.log r))/2 := by
        gcongr
        simpa only [mul_one] using hmul
      _ = Real.exp ((j:ℝ)*(2*Real.log (n:ℝ)-G))/2*r^j := hcombine.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (pow_nonneg hr.le _)
  have hjC : 2*Cbound<(j:ℝ) := hNc.trans_le (by exact_mod_cast hnC.trans hnj)
  have hexp := Real.add_one_le_exp (j:ℝ)
  linarith

end
end IsingBulk.Joint.Negative
