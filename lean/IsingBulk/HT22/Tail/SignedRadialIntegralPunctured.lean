import IsingBulk.HT22.Tail.SignedRadialIntegral
import IsingBulk.HT22.Tail.PuncturedGeometry

/-! Genuine parameter differentiation of the new punctured density and its
signed lifted integral. Cutoffs stay real and outside the descendants. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem puncturedDensity_parameter_differentiable {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      RegularPoint τ B.p B.m s θ) :
    DifferentiableAt ℂ (fun t => puncturedDensity σ d B τ R rcut j t θ) s := by
  by_cases hξ : preferredEqualityCutoff R θ=0
  · simp only [puncturedDensity,hξ,Complex.ofReal_zero,zero_mul]
    exact differentiableAt_const _
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · have hd : 0<preferredAngularDiameter θ := by
        by_contra hn
        exact hξ (preferredEqualityCutoff_zero_germ R θ
          (le_antisymm (le_of_not_gt hn) Metric.diam_nonneg)).self_of_nhds
      exact ((transportedDensity_regularPoint hN σ hσ τ preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j s θ (hreg hb hd)).2).const_mul _
    · have he : (fun t => puncturedDensity σ d B τ R rcut j t θ)=fun _ => 0 := by
        funext t
        simp only [puncturedDensity,
          transportedDensity_right_support σ d B τ rcut hcut j t θ hθ hb,mul_zero]
      rw [he]
      exact differentiableAt_const _

theorem punctured_signed_integral_parameter_hasDerivAt {n : ℕ}
    (c : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (R : ℝ) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (j : ℕ)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (signedLiftedRadialIntegral (n:=n) c B.delta d.alpha (puncturedDensity σ d B τ R rcut j))
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*signedLiftedIntegral (n:=n) c B.delta
        (fun s x => deriv (fun t => puncturedDensity σ d B τ R rcut j t x) s)
        (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
  apply signed_radial_integral_hasDerivAt c B.delta d.alpha _ hε
  · intro u hu q
    have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
        (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAtTotal c z.2)) := by
      apply ContDiff.prodMk
      · have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
        exact ((hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const).comp contDiff_fst
      · exact (constrainedAtTotal_contDiff c).comp contDiff_snd
    exact (puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
      (IsingBulk.Branch.radialParameter d.alpha u) R j (hreg u hu) (constrainedAtTotal c q)).1.comp (u,q) hmap.contDiffAt
  · intro q
    exact puncturedDensity_parameter_differentiable (by omega) σ hσ d B rcut hcut
      (IsingBulk.Branch.radialParameter d.alpha ε) R j _
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c q))
      (hreg ε hε _)

end
end IsingBulk.HT22.Tail
