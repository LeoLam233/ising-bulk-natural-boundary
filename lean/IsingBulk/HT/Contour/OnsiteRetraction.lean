import IsingBulk.HT.Contour.OnsiteIntegration
import IsingBulk.Tail.SelectorTheorem

/-! Exact onsite F+K+S identity, integrating the whole homotopy interval
before any current split and retaining the literal physical source. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem onsitePulledDensity_original {N : ℕ} (f : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    onsitePulledDensity f r τ 0 s θ = (N.factorial:ℂ)⁻¹*angleProductJacobian r θ*
      onsiteCanceledDensity (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ) := by
  unfold onsitePulledDensity
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

theorem onsiteHomotopyTotal_zero_eq_source (N : ℕ) (f : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) :
    onsiteHomotopyTotal N f r τ 0 s = onsiteSourceIntegral N r s := by
  unfold onsiteHomotopyTotal onsiteSourceIntegral
  simp_rw [onsitePulledDensity_original]

 theorem onsite_fixedDensity_contDiff {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    ContDiff ℝ ∞ (onsitePulledDensity (N := N) f r τ lam s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (onsitePulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ).comp
      θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem onsite_weighted_joint_contDiffAt {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) =>
      (angularSelector f p.2:ℂ)*onsitePulledDensity f r τ p.1 s p.2) (lam,θ) := by
  exact ((complexSelector_contDiff f hf).comp contDiff_snd).contDiffAt.mul
    (onsitePulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)

 theorem onsite_weighted_parameter_deriv {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    deriv (fun u => (angularSelector f θ:ℂ)*onsitePulledDensity f r τ u s θ) lam =
      (angularSelector f θ:ℂ)*deriv (fun u => onsitePulledDensity f r τ u s θ) lam := by
  have hj := onsitePulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ
  have hu : DifferentiableAt ℝ (fun u => onsitePulledDensity f r τ u s θ) lam :=
    (hj.comp lam (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact (hu.hasDerivAt.const_mul (angularSelector f θ:ℂ)).deriv

 theorem onsite_homotopyTotal_invariant (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    onsiteHomotopyTotal (n+1) f r τ 1 s = onsiteHomotopyTotal (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => onsitePulledDensity f r τ p.1 s p.2) (fun lam hlam θ =>
      onsitePulledDensity_joint_contDiffAt (by omega) f hr hr1 hτ hlam s hmargin
        hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)
  have hz : (∫ lam : ℝ in 0..1, ∫ θ in angleBox (n+1),
      deriv (fun u => onsitePulledDensity f r τ u s θ) lam) = 0 := by
    calc
      _ = ∫ _lam : ℝ in 0..1, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
        exact onsite_source_spatial_unweighted n f hf hr hr1 hτ hl.1 s hmargin
      _ = 0 := by simp
  rw [hz] at hFTC
  exact sub_eq_zero.mp hFTC.symm

 theorem onsite_namedCurrent_continuous {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    Continuous (fun θ => onsiteNamedCurrentDensity f r τ lam s q θ) := by
  have hU := (onsite_fixedDensity_contDiff hN f hf hr hr1 hτ hlam s hmargin).continuous
  have ha := hf.a_smooth.continuous
  have ha' := hf.a_smooth.continuous_deriv (by simp)
  have hn : Continuous (namedSelectorDerivative (N := N) f q) := by
    unfold namedSelectorDerivative
    fun_prop
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp hn)).mul hU)

 theorem onsite_currentIntegral_eq_difference (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    onsiteCurrentIntegral (n+1) f r τ s =
      onsiteHomotopyLower (n+1) f r τ 1 s-onsiteHomotopyLower (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => (angularSelector f p.2:ℂ)*onsitePulledDensity f r τ p.1 s p.2)
    (fun lam hlam θ => onsite_weighted_joint_contDiffAt (by omega) f hf hr hr1 hτ hlam s hmargin θ)
  unfold onsiteHomotopyLower
  dsimp only at hFTC
  rw [← hFTC]
  unfold onsiteCurrentIntegral
  apply intervalIntegral.integral_congr
  intro lam hlam
  have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
  simp_rw [onsite_weighted_parameter_deriv (N := n+1) (by omega) f hf hr hr1 hτ hl.1 s hmargin]
  rw [onsite_source_spatial_current n f hf hr hr1 hτ hl.1 s hmargin]
  exact (integral_finsetSum _ (fun i _ =>
    (onsite_namedCurrent_continuous (by omega) f hf hr hr1 hτ hl.1 s hmargin i).continuousOn.integrableOn_compact isCompact_Icc)).symm

 theorem onsite_homotopyTotal_selected_split (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    onsiteHomotopyTotal N f r τ 1 s = onsiteSelectedIntegral N f r τ s+onsiteHomotopyLower N f r τ 1 s := by
  have hU := (onsite_fixedDensity_contDiff (lam := 1) hN f hf hr hr1 hτ (by norm_num) s hmargin).continuous
  have hw := (complexSelector_contDiff (N := N) f hf).continuous
  have hs : IntegrableOn (fun θ : Fin N → ℝ =>
      ((1-angularSelector f θ:ℝ):ℂ)*onsitePulledDensity f r τ 1 s θ) (angleBox N) := by
    have hc : Continuous (fun θ : Fin N → ℝ =>
        ((1-angularSelector f θ:ℝ):ℂ)*onsitePulledDensity f r τ 1 s θ) := by
      convert ((continuous_const (y := (1:ℂ))).sub hw).mul hU using 1
      funext θ
      simp only [Complex.ofReal_sub,Complex.ofReal_one,Pi.mul_apply,Pi.sub_apply]
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn (fun θ : Fin N → ℝ =>
      (angularSelector f θ:ℂ)*onsitePulledDensity f r τ 1 s θ) (angleBox N) :=
    (hw.mul hU).continuousOn.integrableOn_compact isCompact_Icc
  unfold onsiteHomotopyTotal onsiteSelectedIntegral onsiteHomotopyLower
  rw [← integral_add hs hk]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  push_cast
  ring

/-- Full onsite source identity, uniform in every positive particle number.
No onsite contour identity, derivative exchange or boundary cancellation is
assumed; each has been proved above on the actual legal homotopy. -/
theorem exact_onsite_weighted_retraction
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    onsiteSourceIntegral N r s = onsiteSelectedIntegral N f r τ s+
      onsiteOriginalLowerIntegral N f r τ s+onsiteCurrentIntegral N f r τ s := by
  cases N with
  | zero => omega
  | succ n =>
    rw [← onsiteHomotopyTotal_zero_eq_source (n+1) f r τ s,
      ← onsite_homotopyTotal_invariant n f hf hr hr1 hτ s hmargin,
      onsite_homotopyTotal_selected_split (n+1) (by omega) f hf hr hr1 hτ s hmargin,
      onsite_currentIntegral_eq_difference n f hf hr hr1 hτ s hmargin]
    change onsiteSelectedIntegral (n+1) f r τ s+onsiteHomotopyLower (n+1) f r τ 1 s =
      onsiteSelectedIntegral (n+1) f r τ s+onsiteHomotopyLower (n+1) f r τ 0 s+
        (onsiteHomotopyLower (n+1) f r τ 1 s-onsiteHomotopyLower (n+1) f r τ 0 s)
    ring


end
end IsingBulk.HT.Contour
