import IsingBulk.Tail.ParameterSmoothAlgebra
import IsingBulk.Tail.MixedFrozenPhase

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def mixedSeparatedDomain {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) : Set (ℂ × (Fin N → ℝ)) :=
  {p | p.1≠0 ∧ (∀ i,0<(sourceW p.1 (deformedPoint f r τ lam p.2 i)).im) ∧
    (∀ i∈J,deformedPoint f r τ lam p.2 i-(deformedPoint f r τ lam p.2 i)⁻¹≠0) ∧
    mixedSourceSlope p.1 (deformedPoint f r τ lam p.2 j)-
      mixedSourceSlope p.1 (deformedPoint f r τ lam p.2 q)≠0 ∧
    1-coordinateProduct (deformedPoint f r τ lam p.2)≠0}

theorem deformedPoint_fixed_contDiff {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ContDiff ℝ ∞ (fun θ => deformedPoint f r τ lam θ i) := by
  have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  unfold deformedPoint retractionShift occupancy
  fun_prop

theorem mixedSeparated_y_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam) (fun _ θ => deformedPoint f r τ lam θ i) :=
  ParameterSmoothOn.angular _ _ (deformedPoint_fixed_contDiff f r τ lam hp hm i)

theorem mixedSeparated_W_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => sourceW s (deformedPoint f r τ lam θ i)) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  have hs := ParameterSmoothOn.parameter Ω
  have hy := mixedSeparated_y_smooth J j q f r τ lam hp hm i
  have hyn : ∀ p∈Ω,deformedPoint f r τ lam p.2 i≠0 := fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i
  exact (hs.add (hs.inv (fun _ h => h.1))).sub
    ((hy.add (hy.inv hyn)).div (ParameterSmoothOn.const Ω 2) (by intro p _; norm_num))

theorem mixedSeparated_phase_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => mixedSourcePhase s (deformedPoint f r τ lam θ i)) :=
  (mixedSeparated_W_smooth J j q f hr τ lam hp hm i).complex_comp lowerArccos
    (fun _ h => lowerArccos_analytic_upper (h.2.1 i))

theorem mixedSeparated_slope_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => mixedSourceSlope s (deformedPoint f r τ lam θ i)) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  have hy := mixedSeparated_y_smooth J j q f r τ lam hp hm i
  have hyi := hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i)
  have hsin := (mixedSeparated_phase_smooth J j q f hr τ lam hp hm i).complex_comp Complex.sin (by intro p _; fun_prop)
  exact ((ParameterSmoothOn.const Ω Complex.I).mul (hy.sub hyi)).div
    ((ParameterSmoothOn.const Ω 2).mul hsin)
    (fun p h => mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (h.2.1 i)))

theorem mixedSeparatedDomain_isOpen {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    IsOpen (mixedSeparatedDomain J j q f r τ lam) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hpΩ
  have hs := continuous_fst.continuousAt.eventually_ne hpΩ.1
  have hW : ∀ᶠ z in 𝓝 p,∀ i,0<(sourceW z.1 (deformedPoint f r τ lam z.2 i)).im :=
    eventually_all.mpr (fun i =>
      (Complex.continuous_im.continuousAt.comp ((mixedSeparated_W_smooth J j q f hr τ lam hp hm i) p hpΩ).1.continuousAt).eventually
        (Ioi_mem_nhds (hpΩ.2.1 i)))
  have hy (i : Fin N) : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam z.2 i) p :=
    ((mixedSeparated_y_smooth J j q f r τ lam hp hm i) p hpΩ).1.continuousAt
  have hbranch : ∀ᶠ z in 𝓝 p,∀ i∈J,deformedPoint f r τ lam z.2 i-(deformedPoint f r τ lam z.2 i)⁻¹≠0 :=
    J.eventually_all.mpr (fun i hi => ((hy i).sub ((hy i).inv₀
      (deformedPoint_nonzero f hr.ne' τ lam p.2 i))).eventually_ne (hpΩ.2.2.1 i hi))
  have hsep := (((mixedSeparated_slope_smooth J j q f hr τ lam hp hm j) p hpΩ).1.continuousAt.sub
    ((mixedSeparated_slope_smooth J j q f hr τ lam hp hm q) p hpΩ).1.continuousAt).eventually_ne hpΩ.2.2.2.1
  have hY : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => 1-coordinateProduct (deformedPoint f r τ lam z.2)) p :=
    continuousAt_const.sub ((ParameterSmoothOn.prod Finset.univ
      (fun i (_ : ℂ) θ => deformedPoint f r τ lam θ i)
      (fun i _ => mixedSeparated_y_smooth J j q f r τ lam hp hm i) p hpΩ).1.continuousAt)
  filter_upwards [hs,hW,hbranch,hsep,hY.eventually_ne hpΩ.2.2.2.2] with z hz0 hzW hzB hzS hzY
  exact ⟨hz0,hzW,hzB,hzS,hzY⟩

end
end IsingBulk.Tail
