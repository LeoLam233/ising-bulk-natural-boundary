import IsingBulk.Tail.CompactPhaseSymmetry
import IsingBulk.Tail.SelectorSmoothDensity

/-! Actual global real angular regularity on the genuine damping domain.
Complex analyticity belongs to the root/phase scalar maps, not the bumps. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem continuedPhase_analyticAt_upper {W : ℂ} (hW : 0<W.im) :
    AnalyticAt ℂ continuedPhase W := by
  apply continuedPhase_analyticAt
  refine ⟨Or.inl (Or.inl hW),?_⟩
  change continuedRoot W ∈ Complex.slitPlane
  rw [continuedRoot_eq_interiorRoot hW]
  exact Or.inr (interiorRoot_lower_im hW).ne

theorem currentPhase_coordinate_contDiff {N : ℕ} (hN : 0<N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0≤f.p x) (hm0 : ∀ x, 0≤f.m x)
    (hps : ∀ x, Real.sin x≤0 → f.p x=0) (hms : ∀ x, 0≤Real.sin x → f.m x=0)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) (i : Fin N) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => continuedPhase (sourceW s (deformedPoint f r τ lam θ i))) := by
  have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  have hy : ContDiff ℝ ∞ (fun θ : Fin N → ℝ => deformedPoint f r τ lam θ i) := by
    unfold deformedPoint retractionShift occupancy
    fun_prop
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im :=
    (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp0 hm0 hps hms i)
  have hwy : ContDiffAt ℝ ∞ (fun θ : Fin N → ℝ => sourceW s (deformedPoint f r τ lam θ i)) θ := by
    unfold sourceW
    exact contDiffAt_const.sub ((hy.contDiffAt.add (hy.contDiffAt.inv
      (deformedPoint_nonzero f hr.ne' τ lam θ i))).div_const 2)
  have hphase : ContDiffAt ℝ ∞ continuedPhase (sourceW s (deformedPoint f r τ lam θ i)) :=
    (continuedPhase_analyticAt_upper hW).contDiffAt.restrict_scalars ℝ
  exact hphase.comp θ (f := fun x : Fin N → ℝ => sourceW s (deformedPoint f r τ lam x i)) hwy

theorem currentComplexPhase_contDiff {N : ℕ} (hN : 0<N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0≤f.p x) (hm0 : ∀ x, 0≤f.m x)
    (hps : ∀ x, Real.sin x≤0 → f.p x=0) (hms : ∀ x, 0≤Real.sin x → f.m x=0)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) :
    ContDiff ℝ ∞ (currentComplexPhase (N := N) f r τ lam s) :=
  ContDiff.sum (fun i _ => currentPhase_coordinate_contDiff hN f hr hr1 hτ hlam hp hm hp0 hm0 hps hms hmargin i)

theorem currentUnwrappedPhase_contDiff {N : ℕ} (hN : 0<N) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0≤f.p x) (hm0 : ∀ x, 0≤f.m x)
    (hps : ∀ x, Real.sin x≤0 → f.p x=0) (hms : ∀ x, 0≤Real.sin x → f.m x=0)
    {s : ℂ} (hmargin : r⁻¹-r<(sourceS s).im) :
    ContDiff ℝ ∞ (currentUnwrappedPhase (N := N) f r τ lam s) := by
  have he : currentUnwrappedPhase (N := N) f r τ lam s=fun θ => (currentComplexPhase f r τ lam s θ).re :=
    funext (currentUnwrappedPhase_eq_re f r τ lam s)
  rw [he]
  exact Complex.reCLM.contDiff.comp
    (currentComplexPhase_contDiff hN f hr hr1 hτ hlam hp hm hp0 hm0 hps hms hmargin)

theorem unwrappedLogY_contDiff {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => unwrappedLogY f r τ lam θ) := by
  have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  unfold unwrappedLogY retractionShift occupancy
  fun_prop

end
end IsingBulk.Tail
