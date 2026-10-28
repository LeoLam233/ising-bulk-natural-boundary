import IsingBulk.HT22.Selected.ContinuedDensity
import IsingBulk.HT22.Physical.ContourDensity

/-! The selected continuation is the germ of the literal physical odd
bordered density, not an even-particle substitute. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open Filter IsingBulk.Preferred22
open scoped Topology BigOperators

theorem selectedContinuedDensity_physical_germ (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (θ : Fin (2*n+1) → ℝ) :
    selectedContinuedDensity (Physical.constraintSign negative) d B ε τ θ
      =ᶠ[𝓝 (IsingBulk.Branch.radialParameter d.alpha ε)]
      (fun t => Physical.bareContourDensity negative τ B.p B.m t θ) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hs : s≠0 := by
    dsimp [s,IsingBulk.Branch.radialParameter]
    exact mul_ne_zero (by exact_mod_cast (show 1+ε≠0 by linarith)) (Complex.exp_ne_zero _)
  have hz : ∀ᶠ t in 𝓝 s, ∀ i : Fin (2*n+1),
      preferredSelectedContinuedRoot d B ε τ θ i t =
        physicalRoot (temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i)) :=
    eventually_all.mpr (fun i => preferred_selected_continued_root_germ d B hε hτ θ i)
  have hW : ∀ᶠ t in 𝓝 s, ∀ i : Fin (2*n+1),
      0<(temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℂ =>
        (temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m θ i)).im) s := by
      unfold temperatureTrace
      exact Complex.continuous_im.continuousAt.comp
        ((continuousAt_id.add (continuousAt_id.inv₀ hs)).sub continuousAt_const)
    have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos])
    exact continuousAt_const.eventually_lt hc ((mul_pos hε hsin).trans_le
      (preferredActualW_im_lower d B hε.le hτ θ i))
  filter_upwards [hz,hW] with t ht hWt
  rw [Physical.bareContourDensity_eq_bordered negative n τ B.p B.m t θ hWt]
  simp only [selectedContinuedDensity,ht,Physical.oneBody_eq_rational,oneBody,Nat.add_sub_cancel]
  ring

end
end IsingBulk.HT22.Selected
