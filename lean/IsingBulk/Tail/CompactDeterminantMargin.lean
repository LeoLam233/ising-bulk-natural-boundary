import IsingBulk.Tail.CompactDeterminantJets
import IsingBulk.Tail.CompactPhaseAbsoluteJets
import IsingBulk.Tail.IntermediateWindow

/-! Quantitative transverse derivative of the actual complex freezing
 determinant. The N-polynomial perturbation is explicit and uniform. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem actual_current_determinant_transverse_perturbation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ N : ℕ, 0<N → ∀ eps τ lam : ℝ,
      0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → eps+lam≤r →
      ∀ θ : Fin N → ℝ,
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      ∀ i j : Fin N, i≠j →
      ‖fderiv ℝ (currentAngularDeterminant f (Real.exp (-d.c₀*eps)) τ lam
          (radialParameter d.theta eps) i j) θ (Pi.single i 1)-
        (-Complex.I*((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i):ℝ):ℂ))‖≤
          C*(N:ℝ)^2*(eps+lam) := by
  obtain ⟨CF,hCF,hFjet⟩ := unwrappedLogY_coordinate_jet_perturbation f hf
  obtain ⟨rG,CG,hrG,hCG,hGjet⟩ := currentPhase_coordinate_jet_perturbation d hcsmall f hf hp1 hδ hδsmall
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  have hγ : 0<min (δ/2) ((1+Real.cos d.thetaB)/2) := lt_min (half_pos hδ) (half_pos hS)
  have hmargin := right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall
  have hstrict : ∀ a∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a|<1 := fun a ha => lt_of_le_of_lt (hmargin a ha) (by linarith)
  obtain ⟨rB,B,hrB,hB,habs⟩ := actual_compact_phase_absolute_jets d f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic (fun x => ⟨hf.p_nonneg x,hp1 x⟩)
    (fun x => ⟨hf.m_nonneg x,hf.m_le_one x⟩) hstrict 2
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min rG (min rB (e/2)),4*CF*B+2*CG,
    lt_min hrG (lt_min hrB (half_pos he)),by positivity,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmall θ hθ i j hij
  have hsmallG := hsmall.trans (min_le_left _ _)
  have hsmallB := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsE : eps<e := by
    have hh := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := unwrappedLogY (N := N) f r τ lam
  let G := currentComplexPhase (N := N) f r τ lam s
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(sourceS s).im := by
    have hh := radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  have hFs : ContDiff ℝ ∞ F := unwrappedLogY_contDiff f r τ lam hf.p_smooth hf.m_smooth
  have hGs : ContDiff ℝ ∞ G := currentComplexPhase_contDiff hN f hr hr1 hτ hlam
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  have hFcoef (l p : Fin N) := hFjet N hN r τ lam hτ hτ1 hlam θ l p
  have hGcoef (l p : Fin N) := hGjet N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmallG θ hθ l p
  have hjets := habs N hN eps τ lam heps.le hτ hτ1 hlam hlam1 hsmallB θ hθ
  have hB1 (l : Fin N) : ‖fderiv ℝ G θ (Pi.single l 1)‖≤B*N := by
    have hh := (iteratedFDeriv ℝ 1 G θ).le_opNorm (fun _ : Fin 1 => Pi.single l (1:ℝ))
    simp only [iteratedFDeriv_one_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      Pi.norm_single,norm_one,one_pow,mul_one] at hh
    exact hh.trans (hjets 1 (by decide))
  have hB2 (l p : Fin N) : ‖fderiv ℝ (fderiv ℝ G) θ (Pi.single p 1) (Pi.single l 1)‖≤B*N := by
    have hh := (iteratedFDeriv ℝ 2 G θ).le_opNorm ![Pi.single p (1:ℝ),Pi.single l (1:ℝ)]
    simp only [iteratedFDeriv_two_apply,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Pi.norm_single,norm_one,mul_one] at hh
    exact hh.trans (hjets 2 le_rfl)
  have he := complex_determinant_transverse_perturbation
    (by positivity : 0≤CF*N*lam) (by positivity : 0≤B*N)
    (hFcoef i i).1 (hFcoef j i).1 (hFcoef i i).2 (hFcoef j i).2
    (hB1 i) (hB1 j) (hB2 i i) (hB2 j i)
    (by simpa only [ite_true] using (hGcoef i i).2)
    (by simpa only [hij,ite_false,sub_zero] using (hGcoef j i).2)
  change ‖fderiv ℝ (angularPairDeterminant F G i j) θ (Pi.single i 1)-_‖≤_
  rw [angularPairDeterminant_fderiv hFs hGs]
  apply he.trans
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hNN : (N:ℝ)≤(N:ℝ)^2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left (show lam≤eps+lam by linarith)
    (show 0≤4*CF*B*(N:ℝ)^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hNN (show 0≤2*CG by positivity)) (show 0≤eps+lam by linarith)
  nlinarith only [h₁,h₂]


theorem intermediate_window_current_power_small (D β b : ℝ) (m : ℕ)
    (hD : 0≤D) (hβ : 0<β) (hb : 0<b) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, (N:ℝ)≤D*Real.sqrt H →
      ∀ lam : ℝ, 0≤lam → lam≤Real.exp (-β*H) →
      (N:ℝ)^m*(Real.exp (-H)+lam)<b := by
  filter_upwards [intermediate_window_uniform_small D 0 1 m hD le_rfl zero_lt_one (b/2) (half_pos hb),
    intermediate_window_uniform_small D 0 β m hD le_rfl hβ (b/2) (half_pos hb)] with H h1 h2
  intro N hN lam _ hlam
  have hh1 := h1 N hN
  have hh2 := h2 N hN
  simp only [zero_mul,Real.exp_zero,mul_one,neg_mul,one_mul] at hh1 hh2
  have hh := mul_le_mul_of_nonneg_left hlam (pow_nonneg (Nat.cast_nonneg N) m)
  simp only [neg_mul] at hh
  nlinarith

/-- Actual transverse imaginary part stays positive, including at the selected
diagonal. A single H threshold works for all intermediate N and lambda. -/
theorem actual_current_determinant_transverse_margin (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ τ lam : ℝ, 0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      ∀ θ : Fin N → ℝ,
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      ∀ i j : Fin N, i≠j →
      c≤(fderiv ℝ (currentAngularDeterminant f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
          (radialParameter d.theta (Real.exp (-H))) i j) θ (Pi.single i 1)).im := by
  obtain ⟨r,C,hr,hC,hperturb⟩ := actual_current_determinant_transverse_perturbation d hcsmall f hf hp1 hδ hδsmall
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  let γ := min (δ/2) ((1+Real.cos d.thetaB)/2)
  have hγ : 0<γ := lt_min (half_pos hδ) (half_pos hS)
  let cR := (1+Real.cos d.thetaB)*γ
  have hcR : 0<cR := mul_pos hS hγ
  refine ⟨cR/2,half_pos hcR,?_⟩
  filter_upwards [intermediate_window_current_power_small D β (min r (cR/(2*C))) 2 hD hβ
    (lt_min hr (div_pos hcR (by positivity))),eventually_ge_atTop (0:ℝ)] with H hsmall hH
  intro N hN hND τ lam hτ hτ1 hlam hlamB θ hθ i j hij
  let eps := Real.exp (-H)
  have heps : 0<eps := Real.exp_pos _
  have hNs : (1:ℝ)≤N := by exact_mod_cast hN
  have hNs2 : (1:ℝ)≤(N:ℝ)^2 := by nlinarith
  have hs := hsmall N hND lam hlam hlamB
  have hsmallR : eps+lam≤r := by
    have hh := hs.trans_le (min_le_left _ _)
    change (N:ℝ)^2*(eps+lam)<r at hh
    nlinarith
  have hlam1 : lam≤1 := hlamB.trans (Real.exp_le_one_iff.mpr (by nlinarith))
  have hp := hperturb N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmallR θ hθ i j hij
  have herr : C*(N:ℝ)^2*(eps+lam)≤cR/2 := by
    have hh := hs.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (show 0<2*C by positivity)).mp hh
    change (N:ℝ)^2*(eps+lam)*(2*C)<cR at hh'
    nlinarith only [hh']
  have hi := (abs_le.mp ((Complex.abs_im_le_norm _).trans (hp.trans herr))).1
  simp only [Complex.sub_im,Complex.neg_im,Complex.mul_im,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im] at hi
  have hcurv := compactRightPhase_uniform_curvature hS hγ (θ i)
    (right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall _ (hθ i))
  have hcurv' : deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i)≤-cR := by
    simpa only [cR,neg_mul] using hcurv
  change cR/2≤_
  linarith

end
end IsingBulk.Tail
