import IsingBulk.Preferred22.DerivativePartition
import IsingBulk.Preferred22.RightDerivativeTail

/-! Convert genuine radial derivative identities of the actual right
integrals into the exact complex iterated derivatives of their physical
zeroth integral. Holomorphy of that original integral is already proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff

/-- The unchanged complete right integral on the selected radial path. -/
def preferredRightRadialIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ) : ℂ :=
  preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε)

/-- Radial uniqueness of derivatives gives the exact complex iterated
integral identity. The derivative premise here is the pointwise conclusion
of the separate punctured Stokes/uniform-limit proof. -/
theorem preferred_right_iterated_integral_of_radial_derivatives (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ ε₀ : ℝ} (hτ : 0≤τ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut)
    (hrper : Function.Periodic rcut (2*Real.pi)) (k : ℕ)
    (hderiv : ∀ j : ℕ,j<k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      HasDerivAt (preferredRightRadialIntegral n d B τ rcut j)
        (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredRightRadialIntegral n d B τ rcut (j+1) ε) ε) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
        preferredPopulationCutoff B.p B.m rcut 0) (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredRightRadialIntegral n d B τ rcut j ε := by
  let I := preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut 0
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hI (ε : ℝ) (hε : 0<ε) : AnalyticAt ℂ I (IsingBulk.Branch.radialParameter d.alpha ε) :=
    preferredTransportedIntegral_zero_analyticAt n d B .right hτ preferredPopulationCutoff rcut
      preferredPopulationCutoff_smooth hr hrper (preferredRadialTrace_im_pos d hε)
  intro j
  induction j with
  | zero => intro _ ε _; rfl
  | succ j ih =>
    intro hj ε hε
    have he : (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        =ᶠ[𝓝 ε] preferredRightRadialIntegral n d B τ rcut j := by
      filter_upwards [isOpen_Ioo.mem_nhds hε] with t ht
      exact ih (by omega) t ht
    have hf : HasDerivAt (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        (ζ*iteratedDeriv (j+1) I (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
      have ha : AnalyticAt ℂ I ((1+(ε:ℂ))*ζ) := by
        simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
          using hI ε hε.1
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
        using preferred_radial_iterated_hasDerivAt ζ ε j ha
    have hg := hderiv j (by omega) ε hε
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)

end
end IsingBulk.Preferred22
