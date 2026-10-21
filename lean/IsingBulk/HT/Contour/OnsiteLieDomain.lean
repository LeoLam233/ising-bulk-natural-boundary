import IsingBulk.HT.Lie.OnsiteTransport
import IsingBulk.HT.Contour.OnsiteDensity
import IsingBulk.Tail.MixedSeparatedDensity

/-! Actual onsite smooth domain. There is no selected slope difference and
no global product pole; only the true branch-coordinate derivative is inverted. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def onsiteLieDomain {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) : Set (ℂ × (Fin N → ℝ)) :=
  {p | p.1≠0 ∧ (∀ i,0<(sourceW p.1 (deformedPoint f r τ lam p.2 i)).im) ∧
    ∀ i∈J,deformedPoint f r τ lam p.2 i-(deformedPoint f r τ lam p.2 i)⁻¹≠0}

theorem onsiteLie_y_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam) (fun _ θ => deformedPoint f r τ lam θ i) :=
  ParameterSmoothOn.angular _ _ (deformedPoint_fixed_contDiff f r τ lam hp hm i)

theorem onsiteLie_W_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => sourceW s (deformedPoint f r τ lam θ i)) := by
  let Ω := onsiteLieDomain J f r τ lam
  have hs := ParameterSmoothOn.parameter Ω
  have hy := onsiteLie_y_smooth J f r τ lam hp hm i
  have hyn : ∀ p∈Ω,deformedPoint f r τ lam p.2 i≠0 :=
    fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i
  exact (hs.add (hs.inv (fun _ h => h.1))).sub
    ((hy.add (hy.inv hyn)).div (ParameterSmoothOn.const Ω 2) (by intro p _; norm_num))

theorem onsiteLieDomain_isOpen {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    IsOpen (onsiteLieDomain J f r τ lam) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hpΩ
  have hs := continuous_fst.continuousAt.eventually_ne hpΩ.1
  have hW : ∀ᶠ z in 𝓝 p,∀ i,0<(sourceW z.1 (deformedPoint f r τ lam z.2 i)).im :=
    eventually_all.mpr (fun i =>
      (Complex.continuous_im.continuousAt.comp
        ((onsiteLie_W_smooth J f hr τ lam hp hm i) p hpΩ).1.continuousAt).eventually
        (Ioi_mem_nhds (hpΩ.2.1 i)))
  have hy (i : Fin N) : ContinuousAt
      (fun z : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam z.2 i) p :=
    ((onsiteLie_y_smooth J f r τ lam hp hm i) p hpΩ).1.continuousAt
  have hbranch : ∀ᶠ z in 𝓝 p,∀ i∈J,
      deformedPoint f r τ lam z.2 i-(deformedPoint f r τ lam z.2 i)⁻¹≠0 :=
    J.eventually_all.mpr (fun i hi => ((hy i).sub ((hy i).inv₀
      (deformedPoint_nonzero f hr.ne' τ lam p.2 i))).eventually_ne (hpΩ.2.2 i hi))
  filter_upwards [hs,hW,hbranch] with z hz0 hzW hzB
  exact ⟨hz0,hzW,hzB⟩

theorem onsiteLie_root_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => globalRoot s (deformedPoint f r τ lam θ i)) :=
  (onsiteLie_W_smooth J f hr τ lam hp hm i).complex_comp interiorRoot
    (fun _ h => interiorRoot_analyticAt_upper_parameter (h.2.1 i))

theorem onsiteLie_phase_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => mixedSourcePhase s (deformedPoint f r τ lam θ i)) :=
  (onsiteLie_W_smooth J f hr τ lam hp hm i).complex_comp lowerArccos
    (fun _ h => lowerArccos_analytic_upper (h.2.1 i))

theorem onsiteLie_slope_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => mixedSourceSlope s (deformedPoint f r τ lam θ i)) := by
  let Ω := onsiteLieDomain J f r τ lam
  have hy := onsiteLie_y_smooth J f r τ lam hp hm i
  have hyi := hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i)
  have hsin := (onsiteLie_phase_smooth J f hr τ lam hp hm i).complex_comp Complex.sin
    (by intro p _; fun_prop)
  exact ((ParameterSmoothOn.const Ω Complex.I).mul (hy.sub hyi)).div
    ((ParameterSmoothOn.const Ω 2).mul hsin)
    (fun p h => mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (h.2.1 i)))

theorem onsiteLie_volume_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam) (mixedHybridVolume J f r τ lam) :=
  ParameterSmoothOn.prod J _ (fun i _ => onsiteLie_slope_smooth J f hr τ lam hp hm i)

theorem onsiteLie_A_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) (hi : i∈J) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => mixedSourceA s (deformedPoint f r τ lam θ i)) := by
  let Ω := onsiteLieDomain J f r τ lam
  have hsi := ((ParameterSmoothOn.parameter Ω).pow 2).inv (fun _ h => pow_ne_zero _ h.1)
  have hy := onsiteLie_y_smooth J f r τ lam hp hm i
  have hd := ((ParameterSmoothOn.const Ω (-Complex.I)).mul
    (hy.sub (hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i)))).div
    (ParameterSmoothOn.const Ω 2) (by intro p _; norm_num)
  exact ((ParameterSmoothOn.const Ω 1).sub hsi).div hd (fun p h =>
    div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (h.2.2 i hi)) (by norm_num))

theorem onsiteLie_field_smooth {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p)
    (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s θ => onsiteBranchField J f r τ lam s θ i) := by
  by_cases hi : i∈J
  · simpa only [onsiteBranchField,hi,ite_true] using onsiteLie_A_smooth J f hr τ lam hp hm i hi
  · simpa only [onsiteBranchField,hi,ite_false] using
      ParameterSmoothOn.const (onsiteLieDomain J f r τ lam) 0

end
end IsingBulk.HT.Contour
