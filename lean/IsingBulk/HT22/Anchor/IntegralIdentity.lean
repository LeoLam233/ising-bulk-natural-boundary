import IsingBulk.HT22.Anchor.RadialIntegral
import IsingBulk.HT22.Physical.WeightedAnalytic
import IsingBulk.Preferred22.DerivativePartition
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original signed physical anchor integral has every complex derivative
represented by the genuine full fixed-v anchor recurrence. This follows from
actual signed torus Stokes and compact differentiation, not a derivative premise. -/
theorem actual_anchor_integral_identity (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ τ₀ ε₀ : ℝ,0<τ₀ ∧ 0<ε₀ ∧ ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ r : ℝ → ℝ,ContDiff ℝ ∞ r → Function.Periodic r (2*Real.pi) →
      ∀ negative : Bool,∀ n : ℕ,∀ a : Fin (2*n+1),∀ j : ℕ,∀ ε : ℝ,0<ε → ε<ε₀ →
      iteratedDeriv j (Physical.anchorPopulationIntegral negative (2*n) a τ preferredPopulationCutoff B.p B.m r)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      transportedIntegral negative (2*n) a B.delta τ preferredPopulationCutoff B.p B.m r j
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  obtain ⟨δ,ε₀,τ₀,_hδ,_hδa,hε₀,hτ₀,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨τ₀,ε₀,hτ₀,hε₀,?_⟩
  intro τ hτ hτr r hr hrper negative n a
  let I := Physical.anchorPopulationIntegral negative (2*n) a τ preferredPopulationCutoff B.p B.m r
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hpts : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (2*n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x ∧
        ∀ i,x i∈Ioo (-Real.pi-δ) δ :=
    fun ε hε x hx => hframe (2*n+1) (by omega) ε τ hε.1 hε.2 hτ hτr x hx
  have hI (ε : ℝ) (hε : 0<ε) : AnalyticAt ℂ I (IsingBulk.Branch.radialParameter d.alpha ε) :=
    Physical.anchorPopulationIntegral_analyticAt negative (2*n) a d B hτ preferredPopulationCutoff r
      preferredPopulationCutoff_smooth hr (preferredRadialTrace_im_pos d hε)
  intro j
  induction j with
  | zero =>
    intro ε hε _
    exact (transportedIntegral_zero negative n a d B τ hτ r hrper _ (preferredRadialTrace_im_pos d hε)).symm
  | succ j ih =>
    intro ε hε hεr
    have he : (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        =ᶠ[𝓝 ε] (fun t => transportedIntegral negative (2*n) a B.delta τ preferredPopulationCutoff B.p B.m r j
          (IsingBulk.Branch.radialParameter d.alpha t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show ε∈Ioo 0 ε₀ from ⟨hε,hεr⟩)] with t ht
      exact ih t ht.1 ht.2
    have hf : HasDerivAt (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        (ζ*iteratedDeriv (j+1) I (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
      have ha : AnalyticAt ℂ I ((1+(ε:ℂ))*ζ) := by
        simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hI ε hε
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
        using preferred_radial_iterated_hasDerivAt ζ ε j ha
    have hg := integral_radial_hasDerivAt negative d B a r hr j hpts ⟨hε,hεr⟩
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)
end
end IsingBulk.HT22.Anchor
