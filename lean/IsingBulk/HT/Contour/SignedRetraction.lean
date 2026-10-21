import IsingBulk.HT.Contour.SignedIntegration
import IsingBulk.Tail.SelectorTheorem

/-! Exact signed weighted retraction with literal normalized source,
selected, original lower and named-current integrals. The complete interval
[0,1] is integrated before any small/large-current split. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Fixed-radius signed source, with precisely the source angular Jacobian.
For σ=1 it is the established source form factor. -/
def signedSourceIntegral (σ : ℂ) (N : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (N.factorial:ℂ)⁻¹*angleProductJacobian r θ*
    signedCanceledDensity σ (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)

def signedHomotopyTotal (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) : ℂ := ∫ θ in angleBox N, signedPulledDensity σ f r τ lam s θ

def signedHomotopyLower (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*signedPulledDensity σ f r τ lam s θ

theorem signedPulledDensity_original {N : ℕ} (σ : ℂ) (f : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    signedPulledDensity σ f r τ 0 s θ = (N.factorial:ℂ)⁻¹*angleProductJacobian r θ*
      signedCanceledDensity σ (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ) := by
  unfold signedPulledDensity
  rw [deformedPoint_zero,angularJacobian_zero,Matrix.det_diagonal]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*Complex.I^N = (2*(Real.pi:ℂ))⁻¹^N := by
    rw [zpow_neg,zpow_natCast,mul_pow,mul_inv_rev]
    have hi : Complex.I^N ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    rw [mul_assoc,mul_left_comm,inv_mul_cancel₀ hi,mul_one,inv_pow]
  unfold angleProductJacobian angleJacobian
  simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*Complex.I^N*
    (∏ i,anglePoint r (θ i))*_ = _
  rw [mul_assoc (N.factorial:ℂ)⁻¹,he]
  simp only [div_eq_mul_inv,inv_pow,angleTuple]
  ring

theorem signedHomotopyTotal_zero_eq_source (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) :
    signedHomotopyTotal σ N f r τ 0 s = signedSourceIntegral σ N r s := by
  unfold signedHomotopyTotal signedSourceIntegral
  simp_rw [signedPulledDensity_original]

 theorem signed_fixedDensity_contDiff (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    ContDiff ℝ ∞ (signedPulledDensity σ (N := N) f r τ lam s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (signedPulledDensity_joint_contDiffAt σ hσ hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ).comp
      θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem signed_weighted_joint_contDiffAt (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) =>
      (angularSelector f p.2:ℂ)*signedPulledDensity σ f r τ p.1 s p.2) (lam,θ) := by
  exact ((complexSelector_contDiff f hf).comp contDiff_snd).contDiffAt.mul
    (signedPulledDensity_joint_contDiffAt σ hσ hN f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)

 theorem signed_weighted_parameter_deriv (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    deriv (fun u => (angularSelector f θ:ℂ)*signedPulledDensity σ f r τ u s θ) lam =
      (angularSelector f θ:ℂ)*deriv (fun u => signedPulledDensity σ f r τ u s θ) lam := by
  have hj := signedPulledDensity_joint_contDiffAt σ hσ hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ
  have hu : DifferentiableAt ℝ (fun u => signedPulledDensity σ f r τ u s θ) lam :=
    (hj.comp lam (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact (hu.hasDerivAt.const_mul (angularSelector f θ:ℂ)).deriv

 theorem signed_homotopyTotal_invariant (σ : ℂ) (hσ : ‖σ‖ = 1) (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    signedHomotopyTotal σ (n+1) f r τ 1 s = signedHomotopyTotal σ (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => signedPulledDensity σ f r τ p.1 s p.2) (fun lam hlam θ =>
      signedPulledDensity_joint_contDiffAt σ hσ (by omega) f hr hr1 hτ hlam s hmargin
        hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)
  have hz : (∫ lam : ℝ in 0..1, ∫ θ in angleBox (n+1),
      deriv (fun u => signedPulledDensity σ f r τ u s θ) lam) = 0 := by
    calc
      _ = ∫ _lam : ℝ in 0..1, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
        exact signed_source_spatial_unweighted σ hσ n f hf hr hr1 hτ hl.1 s hmargin
      _ = 0 := by simp
  rw [hz] at hFTC
  exact sub_eq_zero.mp hFTC.symm

 theorem signed_namedCurrent_continuous (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    Continuous (fun θ => signedNamedCurrentDensity σ f r τ lam s q θ) := by
  have hU := (signed_fixedDensity_contDiff σ hσ hN f hf hr hr1 hτ hlam s hmargin).continuous
  have ha := hf.a_smooth.continuous
  have ha' := hf.a_smooth.continuous_deriv (by simp)
  have hn : Continuous (namedSelectorDerivative (N := N) f q) := by
    unfold namedSelectorDerivative
    fun_prop
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp hn)).mul hU)

 theorem signed_currentIntegral_eq_difference (σ : ℂ) (hσ : ‖σ‖ = 1) (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    signedCurrentIntegral σ (n+1) f r τ s =
      signedHomotopyLower σ (n+1) f r τ 1 s-signedHomotopyLower σ (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => (angularSelector f p.2:ℂ)*signedPulledDensity σ f r τ p.1 s p.2)
    (fun lam hlam θ => signed_weighted_joint_contDiffAt σ hσ (by omega) f hf hr hr1 hτ hlam s hmargin θ)
  unfold signedHomotopyLower
  dsimp only at hFTC
  rw [← hFTC]
  unfold signedCurrentIntegral
  apply intervalIntegral.integral_congr
  intro lam hlam
  have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
  simp_rw [signed_weighted_parameter_deriv σ hσ (N := n+1) (by omega) f hf hr hr1 hτ hl.1 s hmargin]
  rw [signed_source_spatial_current σ hσ n f hf hr hr1 hτ hl.1 s hmargin]
  exact (integral_finsetSum _ (fun i _ =>
    (signed_namedCurrent_continuous σ hσ (by omega) f hf hr hr1 hτ hl.1 s hmargin i).continuousOn.integrableOn_compact isCompact_Icc)).symm

 theorem signed_homotopyTotal_selected_split (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    signedHomotopyTotal σ N f r τ 1 s = signedSelectedIntegral σ N f r τ s+signedHomotopyLower σ N f r τ 1 s := by
  have hU := (signed_fixedDensity_contDiff σ hσ (lam := 1) hN f hf hr hr1 hτ (by norm_num) s hmargin).continuous
  have hw := (complexSelector_contDiff (N := N) f hf).continuous
  have hs : IntegrableOn (fun θ : Fin N → ℝ =>
      ((1-angularSelector f θ:ℝ):ℂ)*signedPulledDensity σ f r τ 1 s θ) (angleBox N) := by
    have hc : Continuous (fun θ : Fin N → ℝ =>
        ((1-angularSelector f θ:ℝ):ℂ)*signedPulledDensity σ f r τ 1 s θ) := by
      convert ((continuous_const (y := (1:ℂ))).sub hw).mul hU using 1
      funext θ
      simp only [Complex.ofReal_sub,Complex.ofReal_one,Pi.mul_apply,Pi.sub_apply]
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn (fun θ : Fin N → ℝ =>
      (angularSelector f θ:ℂ)*signedPulledDensity σ f r τ 1 s θ) (angleBox N) :=
    (hw.mul hU).continuousOn.integrableOn_compact isCompact_Icc
  unfold signedHomotopyTotal signedSelectedIntegral signedHomotopyLower
  rw [← integral_add hs hk]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  push_cast
  ring

/-- Full signed source identity, uniform in every positive particle number.
No signed contour identity, derivative exchange or boundary cancellation is
assumed; each has been proved above on the actual legal homotopy. -/
theorem exact_signed_weighted_retraction (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    signedSourceIntegral σ N r s = signedSelectedIntegral σ N f r τ s+
      signedOriginalLowerIntegral σ N f r τ s+signedCurrentIntegral σ N f r τ s := by
  cases N with
  | zero => omega
  | succ n =>
    rw [← signedHomotopyTotal_zero_eq_source σ (n+1) f r τ s,
      ← signed_homotopyTotal_invariant σ hσ n f hf hr hr1 hτ s hmargin,
      signed_homotopyTotal_selected_split σ hσ (n+1) (by omega) f hf hr hr1 hτ s hmargin,
      signed_currentIntegral_eq_difference σ hσ n f hf hr hr1 hτ s hmargin]
    change signedSelectedIntegral σ (n+1) f r τ s+signedHomotopyLower σ (n+1) f r τ 1 s =
      signedSelectedIntegral σ (n+1) f r τ s+signedHomotopyLower σ (n+1) f r τ 0 s+
        (signedHomotopyLower σ (n+1) f r τ 1 s-signedHomotopyLower σ (n+1) f r τ 0 s)
    ring

/-- Exact σ=1 attachment to the established physical source form factor. -/
theorem signedSourceIntegral_one_eq_upper (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (r τ : ℝ) (s : ℂ)
    (hr : 0 < r) (hr1 : r < 1) (hmargin : r⁻¹-r < (sourceS s).im) :
    signedSourceIntegral 1 N r s = upperFormFactor N s := by
  rw [← signedHomotopyTotal_zero_eq_source 1 N f r τ s]
  simpa only [signedHomotopyTotal,signedPulledDensity_one,homotopyTotal] using
    homotopyTotal_zero_eq_formFactor N hN f r τ s hr hr1 hmargin

end
end IsingBulk.HT.Contour
