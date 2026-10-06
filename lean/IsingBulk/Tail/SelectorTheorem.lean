import IsingBulk.Tail.SelectorParameterIntegral
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.First.ResidueEndpoint

/-! Exact weighted retraction of the actual normalized source integral.
All homotopy differentiation is on the full fixed interval [0,1]. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

 def homotopyTotal (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, pulledDensity f r τ lam s θ

 def homotopyLower (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*pulledDensity f r τ lam s θ

 theorem fixedDensity_contDiff {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    ContDiff ℝ ∞ (pulledDensity (N := N) f r τ lam s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (pulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ).comp
      θ (contDiffAt_const.prodMk contDiffAt_id)

 theorem weighted_joint_contDiffAt {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) =>
      (angularSelector f p.2:ℂ)*pulledDensity f r τ p.1 s p.2) (lam,θ) := by
  exact ((complexSelector_contDiff f hf).comp contDiff_snd).contDiffAt.mul
    (pulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
      hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)

 theorem weighted_parameter_deriv {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (θ : Fin N → ℝ) :
    deriv (fun u => (angularSelector f θ:ℂ)*pulledDensity f r τ u s θ) lam =
      (angularSelector f θ:ℂ)*deriv (fun u => pulledDensity f r τ u s θ) lam := by
  have hj := pulledDensity_joint_contDiffAt hN f hr hr1 hτ hlam s hmargin
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ
  have hu : DifferentiableAt ℝ (fun u => pulledDensity f r τ u s θ) lam :=
    (hj.comp lam (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact (hu.hasDerivAt.const_mul (angularSelector f θ:ℂ)).deriv

 theorem homotopyTotal_invariant (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    homotopyTotal (n+1) f r τ 1 s = homotopyTotal (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => pulledDensity f r τ p.1 s p.2) (fun lam hlam θ =>
      pulledDensity_joint_contDiffAt (by omega) f hr hr1 hτ hlam s hmargin
        hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero θ)
  have hz : (∫ lam : ℝ in 0..1, ∫ θ in angleBox (n+1),
      deriv (fun u => pulledDensity f r τ u s θ) lam) = 0 := by
    calc
      _ = ∫ _lam : ℝ in 0..1, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
        exact source_spatial_unweighted n f hf hr hr1 hτ hl.1 s hmargin
      _ = 0 := by simp
  rw [hz] at hFTC
  exact sub_eq_zero.mp hFTC.symm

 theorem namedCurrent_continuous {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) (q : Fin N) :
    Continuous (fun θ => namedCurrentDensity f r τ lam s q θ) := by
  have hU := (fixedDensity_contDiff hN f hf hr hr1 hτ hlam s hmargin).continuous
  have ha := hf.a_smooth.continuous
  have ha' := hf.a_smooth.continuous_deriv (by simp)
  have hn : Continuous (namedSelectorDerivative (N := N) f q) := by
    unfold namedSelectorDerivative
    fun_prop
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp hn)).mul hU)

 theorem currentIntegral_eq_difference (n : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (s : ℂ) (hmargin : r⁻¹-r < (sourceS s).im) :
    currentIntegral (n+1) f r τ s =
      homotopyLower (n+1) f r τ 1 s-homotopyLower (n+1) f r τ 0 s := by
  have hFTC := compact_mass_fundamental (n+1)
    (fun p => (angularSelector f p.2:ℂ)*pulledDensity f r τ p.1 s p.2)
    (fun lam hlam θ => weighted_joint_contDiffAt (by omega) f hf hr hr1 hτ hlam s hmargin θ)
  unfold homotopyLower
  dsimp only at hFTC
  rw [← hFTC]
  unfold currentIntegral
  apply intervalIntegral.integral_congr
  intro lam hlam
  have hl : lam ∈ Icc (0:ℝ) 1 := by simpa using hlam
  simp_rw [weighted_parameter_deriv (N := n+1) (by omega) f hf hr hr1 hτ hl.1 s hmargin]
  rw [source_spatial_current n f hf hr hr1 hτ hl.1 s hmargin]
  exact (integral_finsetSum _ (fun i _ =>
    (namedCurrent_continuous (by omega) f hf hr hr1 hτ hl.1 s hmargin i).continuousOn.integrableOn_compact isCompact_Icc)).symm

 theorem homotopyTotal_zero_eq_formFactor (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (r τ : ℝ) (s : ℂ)
    (hr : 0 < r) (hr1 : r < 1) (hmargin : r⁻¹-r < (sourceS s).im) :
    homotopyTotal N f r τ 0 s = upperFormFactor N s := by
  have hroot := globalRoot_admissible hr hr1 hmargin
  have ht (θ : Fin N → ℝ) : ResidueAdmissible r s (angleTuple r θ)
      (fun i => globalRoot s (anglePoint r (θ i))) :=
    hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _)
  rw [upperFormFactor_eq_fixed_radius N hN hr hr1 hmargin,
    (lemma_residue N hN r s (globalRoot s) hroot).1]
  unfold homotopyTotal reducedFormFactor
  simp_rw [pulledDensity_original f r τ s _ (ht _),mul_assoc]
  rw [integral_const_mul,multiCircleIntegral_eq_angle]
  congr 1
  exact (multiAngleIntegral_eq_box N _ (sourceReducedAngularDensity_continuous N hN hr hr1 hmargin)).symm

 theorem homotopyTotal_selected_split (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    homotopyTotal N f r τ 1 s = selectedIntegral N f r τ s+homotopyLower N f r τ 1 s := by
  have hU := (fixedDensity_contDiff (lam := 1) hN f hf hr hr1 hτ (by norm_num) s hmargin).continuous
  have hw := (complexSelector_contDiff (N := N) f hf).continuous
  have hs : IntegrableOn (fun θ : Fin N → ℝ =>
      ((1-angularSelector f θ:ℝ):ℂ)*pulledDensity f r τ 1 s θ) (angleBox N) := by
    have hc : Continuous (fun θ : Fin N → ℝ =>
        ((1-angularSelector f θ:ℝ):ℂ)*pulledDensity f r τ 1 s θ) := by
      convert ((continuous_const (y := (1:ℂ))).sub hw).mul hU using 1
      funext θ
      simp only [Complex.ofReal_sub,Complex.ofReal_one,Pi.mul_apply,Pi.sub_apply]
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn (fun θ : Fin N → ℝ =>
      (angularSelector f θ:ℂ)*pulledDensity f r τ 1 s θ) (angleBox N) :=
    (hw.mul hU).continuousOn.integrableOn_compact isCompact_Icc
  unfold homotopyTotal selectedIntegral homotopyLower
  rw [← integral_add hs hk]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  push_cast
  ring

/-- Source prop:selector exact identity, with every integral defined literally
and the full fixed homotopy handled before any tail-window split. -/
 theorem exact_weighted_retraction (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    upperFormFactor N s = selectedIntegral N f r τ s+
      originalLowerIntegral N f r τ s+currentIntegral N f r τ s := by
  cases N with
  | zero => omega
  | succ n =>
    rw [← homotopyTotal_zero_eq_formFactor (n+1) (by omega) f r τ s hr hr1 hmargin,
      ← homotopyTotal_invariant n f hf hr hr1 hτ s hmargin,
      homotopyTotal_selected_split (n+1) (by omega) f hf hr hr1 hτ s hmargin,
      currentIntegral_eq_difference n f hf hr hr1 hτ s hmargin]
    change selectedIntegral (n+1) f r τ s+homotopyLower (n+1) f r τ 1 s =
      selectedIntegral (n+1) f r τ s+homotopyLower (n+1) f r τ 0 s+
        (homotopyLower (n+1) f r τ 1 s-homotopyLower (n+1) f r τ 0 s)
    ring

 theorem retraction_current_support {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (θ : Fin N → ℝ) (q : Fin N) (hq : namedSelectorDerivative f q θ ≠ 0) :
    θ q ∈ Function.support (deriv f.a) ∧ f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧
      f.m (θ q)=0 ∧ deriv f.m (θ q)=0 ∧
      ∀ i, i ≠ q → θ i ∈ tsupport (fun x => 1-f.a x) := by
  obtain ⟨ha,hother⟩ := namedSelectorDerivative_support f θ q hq
  obtain ⟨hp,hp',hm,hm'⟩ := hf.named (θ q) ha
  refine ⟨ha,hp,hp',hm,hm',?_⟩
  intro i hi
  apply subset_closure
  change 1-f.a (θ i) ≠ 0
  exact sub_ne_zero.mpr (Ne.symm (hother i hi))

/-- Complete source proposition: normalized retraction plus the named current
support assertions. The bump setup has a constructed source instance. -/
 theorem proposition_selector (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im) :
    (upperFormFactor N s = selectedIntegral N f r τ s+
      originalLowerIntegral N f r τ s+currentIntegral N f r τ s) ∧
    (∀ θ : Fin N → ℝ, ∀ q : Fin N, namedSelectorDerivative f q θ ≠ 0 →
      θ q ∈ Function.support (deriv f.a) ∧ f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧
      f.m (θ q)=0 ∧ deriv f.m (θ q)=0 ∧
      ∀ i, i ≠ q → θ i ∈ tsupport (fun x => 1-f.a x)) :=
  ⟨exact_weighted_retraction N hN f hf hr hr1 hτ s hmargin,
    fun θ q hq => retraction_current_support f hf θ q hq⟩

end
end IsingBulk.Tail
