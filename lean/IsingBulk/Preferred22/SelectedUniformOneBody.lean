import IsingBulk.Preferred22.SelectedContinuation

/-! A second, fixed-particle selected-sector bound retains the positive
contour displacement instead of the integrable angular envelope. It applies
at order two as well, where fourfold convolution is unavailable. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1100000

lemma preferred_oneBody_quadratic_identity {z W : ℂ} (hz : z≠0)
    (hq : z^2-2*W*z+1=0) (hD : W^2-1≠0) :
    1-z^2≠0 ∧ (oneBody z)^2=(W^2-1)⁻¹ := by
  have he : 1-z^2=2*z*(W-z) := by linear_combination hq
  have hs : (W-z)^2=W^2-1 := by linear_combination hq
  have hd : W-z≠0 := by
    intro h
    rw [h,zero_pow (by decide : 2≠0)] at hs
    exact hD hs.symm
  have hden : 1-z^2≠0 := by rw [he]; exact mul_ne_zero (mul_ne_zero (by norm_num) hz) hd
  have ho : oneBody z=(W-z)⁻¹ := by unfold oneBody; rw [he]; field_simp
  refine ⟨hden,?_⟩
  rw [ho,inv_pow,hs]

lemma preferred_oneBody_quadratic_bound {z W : ℂ} (hz : z≠0)
    (hq : z^2-2*W*z+1=0) {D : ℝ} (hD : 0<D) (hgap : D≤‖W^2-1‖) :
    1-z^2≠0 ∧ ‖oneBody z‖≤(Real.sqrt D)⁻¹ := by
  have hW : W^2-1≠0 := norm_pos_iff.mp (hD.trans_le hgap)
  obtain ⟨hden,he⟩ := preferred_oneBody_quadratic_identity hz hq hW
  have hn := congrArg (fun u : ℂ => ‖u‖) he
  rw [norm_pow,norm_inv] at hn
  have hb : ‖oneBody z‖^2≤D⁻¹ := by rw [hn]; exact inv_anti₀ hD hgap
  have hs : ((Real.sqrt D)⁻¹)^2=D⁻¹ := by rw [inv_pow,Real.sq_sqrt hD.le]
  have hp : 0≤(Real.sqrt D)⁻¹ := by positivity
  exact ⟨hden,by nlinarith [norm_nonneg (oneBody z)]⟩

theorem preferred_selected_continued_oneBody_uniform (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c ρ : ℝ,0<c ∧ 0<ρ ∧ ρ≤1 ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ/(N:ℝ)^3 →
      ∀ i : Fin N,
      AnalyticAt ℂ (fun z => oneBody (preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i z)) t ∧
      ‖oneBody (preferredSelectedContinuedRoot d
        (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t)‖≤(Real.sqrt (c*τ/(N:ℝ)))⁻¹ := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hbranch⟩ := preferred_selected_complete_branch_disk d hcap
  refine ⟨c,ρ,hc,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht i
  let B := cappedCanonicalPreferredBump d cap hcap
  let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
  let V := temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i)
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW : OffRealSegment W := Or.inl (ne_of_gt
    ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ.le θ i)))
  have hD : W^2-1≠0 := offRealSegment_discriminant_ne_zero hW
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hbranch' := hbranch N hN ε τ hε hερ hτ hτρ θ hw t ht i
  obtain ⟨hden,hbound⟩ := preferred_oneBody_quadratic_bound (localPhysicalRoot_ne_zero hD V)
    (localPhysicalRoot_quadratic hD V) (by positivity : 0<c*τ/(N:ℝ)) hbranch'.2
  refine ⟨?_,hbound⟩
  exact (analyticAt_const.mul hbranch'.1).div
    (analyticAt_const.sub (hbranch'.1.pow 2)) hden

end
end IsingBulk.Preferred22
