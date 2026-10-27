import IsingBulk.Preferred22.PhysicalTransport
import IsingBulk.Preferred22.ZerothSourceBound

/-! The complete unchanged physical JH prefactor has exactly the genuine
Jacobian/resolvent already integrated in the occupancy-dependent coarea. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology

/-- Literal JH normalization on the whole one-sided physical source. -/
theorem preferred_source_JH_norm_formula {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (θ : Fin N → ℝ) (hS : 0<(preferredRadialTrace d ε).re)
    (hSδ : (preferredRadialTrace d ε).re<2*Real.cos B.delta)
    (hθ : ∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) :
    ‖preferredCoordinateJacobian τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ *
      preferredSourceResolvent τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ‖=
      ‖(preferredContourMatrix τ B.p B.m θ).det‖*‖1+preferredActualZ d B ε τ θ‖*
        preferredJacobianResolvent d B ε τ θ := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW (i : Fin N) : 0<(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im :=
    (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hinv (i : Fin N) : (preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ i))⁻¹=
      actualBumpSlopeVector d B ε τ θ i+1 :=
    preferred_inverse_Uq_on_source d B ε τ θ i hS hSδ (hθ i) (hW i)
  have hZ : preferredSourceProductPhase τ B.p B.m s θ=preferredActualZ d B ε τ θ :=
    preferredSourceProductPhase_eq_roots τ B.p B.m s θ hW
  have hH : preferredSourceResolvent τ B.p B.m s θ=
      (1+preferredActualZ d B ε τ θ)/(1-preferredActualZ d B ε τ θ) := by
    change (1+preferredSourceProductPhase τ B.p B.m s θ)/(1-preferredSourceProductPhase τ B.p B.m s θ)=_
    rw [hZ]
  change ‖preferredCoordinateJacobian τ B.p B.m s θ*preferredSourceResolvent τ B.p B.m s θ‖=_
  rw [hH]
  simp only [preferredCoordinateJacobian,norm_mul,norm_prod,norm_div]
  simp_rw [hinv]
  unfold preferredJacobianResolvent
  ring

/-- One fixed determinant constant controls the unchanged JH prefactor for
every derivative order and every actual occupancy configuration. -/
theorem preferred_actual_JH_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ N : ℕ,0<N → ∀ ε τ : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ≤1 → ∀ θ : Fin N → ℝ,
      (∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ‖preferredCoordinateJacobian τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ *
        preferredSourceResolvent τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        2*C^N*preferredJacobianResolvent d B ε τ θ := by
  obtain ⟨C,hC,hdet⟩ := preferred_contour_determinant_bound d B
  obtain ⟨ε₀,hε₀,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_pos])
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτ1 θ hθ
  obtain ⟨hS,_hSi,hSδ⟩ := hmargin ε hε hεr
  have hnum : ‖1+preferredActualZ d B ε τ θ‖≤2 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖preferredActualZ d B ε τ θ‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith [preferredActualZ_norm_le_one d B hε hτ θ]
  rw [preferred_source_JH_norm_formula d B hε hτ θ hS hSδ hθ]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul (hdet N hN τ hτ hτ1 θ) hnum (norm_nonneg _) (by positivity))
    (preferredJacobianResolvent_nonneg d B ε τ θ)
  simpa only [mul_comm] using hh

end
end IsingBulk.Preferred22
