import IsingBulk.Preferred22.WeightedRightPartition

/-! Exact partition of any original smooth right weight by an independent
smooth equality multiplier. This retains the true complex derivatives of
all weighted physical integrals. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredWeightedRightIntegral_factor_partition (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (ψ σ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hσ : ContDiff ℝ ∞ σ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) :
    preferredWeightedRightIntegral n d B σ τ rcut 0 (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredWeightedRightIntegral n d B (fun θ => ψ θ*σ θ) τ rcut 0
        (IsingBulk.Branch.radialParameter d.alpha ε)+
      preferredWeightedRightIntegral n d B (fun θ => (1-ψ θ)*σ θ) τ rcut 0
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  have hi := continuous_integrableOn_angularBox (preferredWeightedRightSeed_continuous n d B hε hτ
    (fun θ => ψ θ*σ θ) (hψ.mul hσ) rcut hr)
  have hj := continuous_integrableOn_angularBox (preferredWeightedRightSeed_continuous n d B hε hτ
    (fun θ => (1-ψ θ)*σ θ) ((contDiff_const.sub hψ).mul hσ) rcut hr)
  unfold preferredWeightedRightIntegral
  rw [←integral_add hi hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [preferredWeightedPhysicalDensity]
    ring

theorem preferredWeightedRightIntegral_derivative_factor_partition (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (ψ σ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hσ : ContDiff ℝ ∞ σ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (j : ℕ) {ε : ℝ} (hε : 0<ε) :
    iteratedDeriv j (preferredWeightedRightIntegral n d B σ τ rcut 0)
      (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j (preferredWeightedRightIntegral n d B (fun θ => ψ θ*σ θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)+
      iteratedDeriv j (preferredWeightedRightIntegral n d B (fun θ => (1-ψ θ)*σ θ) τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let F := preferredWeightedRightIntegral n d B σ τ rcut 0
  let G := preferredWeightedRightIntegral n d B (fun θ => ψ θ*σ θ) τ rcut 0
  let H := preferredWeightedRightIntegral n d B (fun θ => (1-ψ θ)*σ θ) τ rcut 0
  have hf (t : ℝ) (ht : 0<t) : AnalyticAt ℂ F (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ σ hσ rcut hr (preferredRadialTrace_im_pos d ht)
  have hg (t : ℝ) (ht : 0<t) : AnalyticAt ℂ G (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ _ (hψ.mul hσ) rcut hr (preferredRadialTrace_im_pos d ht)
  have hh (t : ℝ) (ht : 0<t) : AnalyticAt ℂ H (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ _ ((contDiff_const.sub hψ).mul hσ)
      rcut hr (preferredRadialTrace_im_pos d ht)
  have hgh (t : ℝ) (ht : 0<t) : AnalyticAt ℂ (fun s => G s+H s)
      (IsingBulk.Branch.radialParameter d.alpha t) := (hg t ht).add (hh t ht)
  have he : ∀t : ℝ,0<t → F (IsingBulk.Branch.radialParameter d.alpha t)=
      G (IsingBulk.Branch.radialParameter d.alpha t)+H (IsingBulk.Branch.radialParameter d.alpha t) :=
    fun t ht => preferredWeightedRightIntegral_factor_partition n d B ht hτ ψ σ hψ hσ rcut hr
  have hc := preferred_radial_iteratedDeriv_congr
    (F := F) (G := fun s => G s+H s) (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hf)
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hgh)
    (by simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using he) j ε hε
  have hc' : iteratedDeriv j F (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j (fun s => G s+H s) (IsingBulk.Branch.radialParameter d.alpha ε) := by
    simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hc
  change iteratedDeriv j F _=iteratedDeriv j G _+iteratedDeriv j H _
  rw [hc',iteratedDeriv_fun_add (hg ε hε).contDiffAt (hh ε hε).contDiffAt]

end
end IsingBulk.Preferred22
