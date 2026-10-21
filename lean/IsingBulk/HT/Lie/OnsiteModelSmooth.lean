import IsingBulk.HT.Lie.OnsiteAllOrder

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsiteLie_phase_smooth {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s x => mixedContourPhase f r τ lam s x i) :=
  (onsiteLie_W_smooth J f hr τ lam hp hm i).complex_comp lowerArccos
    (fun _ hp => lowerArccos_analytic_upper (hp.2.1 i))

theorem onsiteLie_slope_smooth {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (onsiteLieDomain J f r τ lam)
      (fun s x => mixedSourceSlope s (deformedPoint f r τ lam x i)) := by
  let Ω := onsiteLieDomain J f r τ lam
  have hy := onsiteLie_y_smooth J f r τ lam hp hm i
  have hyi := hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i)
  have hsin := (onsiteLie_phase_smooth J f hr τ lam hp hm i).complex_comp Complex.sin
    (by intro p _; fun_prop)
  exact ((ParameterSmoothOn.const Ω Complex.I).mul (hy.sub hyi)).div
    ((ParameterSmoothOn.const Ω 2).mul hsin)
    (fun p h => mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (h.2.1 i)))

theorem onsiteDisplacement_contDiffAt {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ)
    (p : ℂ × (Fin N → ℝ)) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : p∈onsiteLieDomain J f r τ lam) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => onsiteDisplacement J f r τ lam s φ z.1 z.2) p := by
  unfold onsiteDisplacement onsiteModelMap
  apply ContDiffAt.prodMk (contDiffAt_fst.sub contDiffAt_const)
  apply ContDiffAt.prodMk _ contDiffAt_const
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i∈J
  · simpa only [mixedHybridMap,hi,ite_true,Function.uncurry] using
      ((onsiteLie_phase_smooth J f hr τ lam hp hm i) p hΩ).1.sub contDiffAt_const
  · simp only [hi,ite_false]
    exact contDiffAt_const

def onsiteModelDomain {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ) (F : MixedActiveSpace N → ℂ) :
    Set (ℂ × (Fin N → ℝ)) :=
  onsiteLieDomain J f r τ lam ∩
    {p | AnalyticAt ℂ F (onsiteDisplacement J f r τ lam s φ p.1 p.2)}

theorem onsiteModelDomain_isOpen {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (F : MixedActiveSpace N → ℂ) :
    IsOpen (onsiteModelDomain J f r τ lam s φ F) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hpΩ
  have hΩ := (onsiteLieDomain_isOpen J f hr τ lam hp hm).mem_nhds hpΩ.1
  have hA := (onsiteDisplacement_continuousAt J f hr τ lam s φ p hp hm hpΩ.1).eventually ((isOpen_analyticAt ℂ F).mem_nhds hpΩ.2)
  filter_upwards [hΩ,hA] with q hqΩ hqA
  exact ⟨hqΩ,hqA⟩

theorem onsiteRegularModel_smooth {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (F : MixedActiveSpace N → ℂ) :
    ParameterSmoothOn (onsiteModelDomain J f r τ lam s φ F)
      (onsiteRegularModel J f r τ lam s φ F) := by
  intro p hpΩ
  have hv := ParameterSmoothOn.prod J
    (fun i t x => mixedSourceSlope t (deformedPoint f r τ lam x i))
    (fun i _ => onsiteLie_slope_smooth J f hr τ lam hp hm i)
  refine ⟨?_,(onsiteRegularModel_differentiable J f hr τ lam s φ p.1 p.2 hpΩ.1.1 hp hm
    (fun i _ => hpΩ.1.2.1 i) F hpΩ.2.differentiableAt).1⟩
  exact (hv p hpΩ.1).1.mul ((hpΩ.2.contDiffAt.restrict_scalars ℝ).comp p
    (onsiteDisplacement_contDiffAt J f hr τ lam s φ p hp hm hpΩ.1))

end
end IsingBulk.HT.Lie
