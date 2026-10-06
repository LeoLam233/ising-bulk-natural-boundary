import IsingBulk.Tail.MixedSlopeSeparation

/-! Uniform actual contour data used by mixed coefficient estimates.
All bounds precede particle number and retain the full coupled occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem mixed_actual_uniform_source_data (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (t : ℝ) (ht : 0<t) :
    ∃ c e t₀ : ℝ, 0<c ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ, 0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        ‖1-(s^2)⁻¹‖≤5 ∧ ∀ i,
        let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i
        ∃ v : ℝ, |v|≤1 ∧ y=radialAnglePoint v (θ i) ∧
          ‖sourceW s y-(limitingAngularW d.thetaB (θ i):ℂ)‖≤t ∧ 0<(sourceW s y).im := by
  have hb : 0<Real.sin d.thetaB := d.a_pos
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨c,eG,hc,hc1,heG,_heG1,hmargin⟩ := original_disk_trace_margin d.theta d.c₀ hsint d.c₀_pos hcsmall
  let e := min eG (min 1 (min (1/(4*(d.c₀+1))) (t/(8*(d.c₀+2)))))
  let t₀ := min (1/8:ℝ) (t/16)
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  have ht₀ : 0<t₀ := lt_min (by norm_num) (by positivity)
  refine ⟨c,e,t₀,hc,he,ht₀,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let ρ := occupancy (fun i => f.p (θ i))/(N:ℝ)
  let v := fun i : Fin N => coupledRadialExponent d.c₀ eps (lam*τ) 1 (f.p (θ i)) (f.m (θ i)) ρ
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hρ0 : 0≤ρ := div_nonneg (occupancy_nonneg (fun i => (thresholdStep_range _ _ _).1)) hn.le
  have hρ1 : ρ≤1 := (div_le_one hn).mpr (occupancy_le (fun i => (thresholdStep_range _ _ _).2))
  have heG' := hepslt.trans_le (min_le_left eG _)
  have heps1 : eps≤1 := hepslt.le.trans ((min_le_right eG _).trans (min_le_left _ _))
  have hepbase : eps≤1/(4*(d.c₀+1)) := hepslt.le.trans
    ((min_le_right eG _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hept : eps≤t/(8*(d.c₀+2)) := hepslt.le.trans
    ((min_le_right eG _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hte : lam*τ≤1/8 := htl.le.trans (min_le_left _ _)
  have htt : lam*τ≤t/16 := htl.le.trans (min_le_right _ _)
  have hsmall : d.c₀*eps+2*(lam*τ)≤1 := by
    have hh := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<4*(d.c₀+1))).mp hepbase
    nlinarith
  have hyv (i : Fin N) : y i=radialAnglePoint (v i) (θ i) := by
    dsimp [y]
    rw [deformedPoint_scale_lambda,deformedPoint_coupledRadialExponent]
  have hv (i : Fin N) : |v i|≤1 := by
    have hh := coupledRadialExponent_bound (p := f.p (θ i)) (m := f.m (θ i)) d.c₀_pos.le heps.le (mul_nonneg hl0 hτ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
      (thresholdStep_range _ _ _).1 (thresholdStep_range _ _ _).2
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _) hρ0 hρ1
    exact hh.trans hsmall
  have hd (i : Fin N) : ‖sourceW s (y i)-(limitingAngularW d.thetaB (θ i):ℂ)‖≤t := by
    have hh := actual_deformed_sourceW_small_disk_motion d hN f heps.le heps1 (mul_nonneg hl0 hτ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
      (show c*eps≤1/4 by nlinarith)
      (fun x => thresholdStep_range _ _ _) (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
      hsmall θ i hs
    rw [← deformedPoint_scale_lambda] at hh
    have het := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<8*(d.c₀+2))).mp hept
    have hce := mul_le_mul_of_nonneg_right hc1 heps.le
    exact hh.trans (by nlinarith)
  have hm : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps)<(sourceS s).im := by
    simpa only [neg_mul,Real.exp_neg,inv_inv] using hmargin eps heps heG' s hs
  have hr : 0<Real.exp (-d.c₀*eps) := Real.exp_pos _
  have hr1 : Real.exp (-d.c₀*eps)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hphys (i : Fin N) : 0<(sourceW s (y i)).im := by
    have hh := sourceW_upper_of_margin hr hr1 hm (deformedPoint_zero_norm f hr.le τ θ i)
    exact hh.trans_le (deformed_sourceW_im_ge (by omega) f hr hτ hl0 θ s
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.nonneg _)
      (fun x hx => thresholdStep_zero (by linarith) (by linarith))
      (fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x hb hη hηsmall hx) i)
  have hsabs : ‖s-radialParameter d.theta eps‖≤c := hs.trans (mul_le_of_le_one_right hc.le heps1)
  have hsn : 1/2≤‖s‖ := (selected_disk_parameter_envelope (N := 1) (by norm_num) heps.le heps1
    (by linarith : c≤1/4) (by simpa using hsabs)).1
  have hsinv : ‖s⁻¹‖≤2 := by
    rw [norm_inv,inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0<‖s‖)).mpr
    linarith
  have hderiv : ‖1-(s^2)⁻¹‖≤5 := by
    have hh := norm_sub_le (1:ℂ) ((s^2)⁻¹)
    rw [norm_one,← inv_pow,norm_pow] at hh
    rw [← inv_pow]
    nlinarith [norm_nonneg s⁻¹]
  refine ⟨hderiv,?_⟩
  intro i
  exact ⟨v i,hv i,hyv i,hd i,hphys i⟩

end
end IsingBulk.Tail
