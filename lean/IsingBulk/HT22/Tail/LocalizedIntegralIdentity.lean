import IsingBulk.HT22.Tail.LocalizedObservable
import IsingBulk.HT22.Tail.LocalizedRadialIntegral
import IsingBulk.Preferred22.DerivativePartition

namespace IsingBulk.HT22.Tail
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem localized_integral_identity (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ δB ε₀ : ℝ} (hτ : 0≤τ)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin (2*n+1) → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB (2*n+1), preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (hreg : ∀ε∈Ioo 0 ε₀,∀x∈preferredRightAngularBox d B.delta δB (2*n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x) :
    ∀j : ℕ,∀ε : ℝ,0<ε → ε<ε₀ →
      iteratedDeriv j (localizedObservable negative (2*n) d B τ rcut W)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      signedLiftedIntegral (Physical.constraintAngle negative) B.delta
        (localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W j)
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let I := localizedObservable negative (2*n) d B τ rcut W
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hI (ε : ℝ) (hε : 0<ε) : AnalyticAt ℂ I (IsingBulk.Branch.radialParameter d.alpha ε) :=
    localizedObservable_analyticAt negative (2*n) d B hτ W hW rcut hcut.2.2.1 (preferredRadialTrace_im_pos d hε)
  intro j
  induction j with
  | zero =>
    intro ε hε _
    exact localizedObservable_eq_zero_integral negative n d B hτ W rcut (preferredRadialTrace_im_pos d hε)
  | succ j ih =>
    intro ε hε hεr
    have he : (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        =ᶠ[𝓝 ε] (fun t => signedLiftedIntegral (Physical.constraintAngle negative) B.delta
          (localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W j)
          (IsingBulk.Branch.radialParameter d.alpha t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show ε∈Ioo 0 ε₀ from ⟨hε,hεr⟩)] with t ht
      exact ih t ht.1 ht.2
    have hf : HasDerivAt (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        (ζ*iteratedDeriv (j+1) I (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
      have ha : AnalyticAt ℂ I ((1+(ε:ℂ))*ζ) := by
        simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hI ε hε
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
        using preferred_radial_iterated_hasDerivAt ζ ε j ha
    have hσ : ‖Physical.constraintSign negative‖≤1 := by rw [Physical.constraintSign_norm]
    have hg := localized_integral_radial_hasDerivAt (Physical.constraintAngle negative) (Physical.constraintSign negative)
      hσ d B rcut hcut W hW hzero j hreg ⟨hε,hεr⟩
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)

/-- Geometry thresholds precede all weights, fixed particle numbers and
orders. There is no high-N collision-degree restriction for a genuinely
separated smooth localized seed. -/
theorem actual_localized_integral_identity (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
    ∃ ε₀ τ₀ δ₀ : ℝ,0<ε₀ ∧0<τ₀ ∧0<δ₀ ∧δ₀<B.delta ∧
    ∀δ : ℝ,δ≤δ₀ → ∀rcut : ℝ→ℝ,PreferredRightCutoffData d B δ rcut →
    ∀n : ℕ,∀W : (Fin (2*n+1)→ℝ)→ℂ,ContDiff ℝ ∞ W →
    (∀x∈preferredRightAngularBox d B.delta δ (2*n+1),preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _=>0) →
    ∀negative : Bool,∀τ : ℝ,0≤τ → τ<τ₀ → ∀j : ℕ,∀ε : ℝ,0<ε → ε<ε₀ →
    iteratedDeriv j (localizedObservable negative (2*n) d B τ rcut W) (IsingBulk.Branch.radialParameter d.alpha ε)=
      signedLiftedIntegral (Physical.constraintAngle negative) B.delta
        (localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W j)
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  obtain ⟨cap,hcap,hcapa,hreg⟩ := actual_regularPoint d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,z,he,ht,hz,hzB,hreg⟩ := hreg B hB
  refine ⟨e,t,z,he,ht,hz,hzB,?_⟩
  intro δ hδ rcut hcut n W hW hzero negative τ hτ hτr
  apply localized_integral_identity negative n d B hτ rcut hcut W hW hzero
  intro ε hε x hx hD
  apply hreg (2*n+1) (by omega) ε τ hε.1 hε.2 hτ hτr x _ hD
  intro i
  exact ⟨by have := (hx i).1; linarith,(hx i).2⟩

end
end IsingBulk.HT22.Tail
