import IsingBulk.HT22.Geometry.SignedJacobian
import IsingBulk.HT22.Tail.PhysicalRecurrence
import IsingBulk.Preferred22.PhysicalJacobianBound

/-! The actual signed physical JH prefactor and the very same coarea density.
The scalar Jacobian is ambient; no tangent regular-coordinate determinant occurs. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem signed_source_JH_norm_formula {N : ℕ} (a : ℝ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (θ : Fin N → ℝ) (hS : 0<(preferredRadialTrace d ε).re)
    (hSδ : (preferredRadialTrace d ε).re<2*Real.cos B.delta)
    (hθ : ∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) :
    ‖coordinateJacobian τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ *
      sourceSignedResolvent (Complex.exp (-Complex.I*(a:ℂ))) τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖=
      ‖(preferredContourMatrix τ B.p B.m θ).det‖*‖1+signedActualZ a d B ε τ θ‖*
        signedJacobianResolvent a d B ε τ θ := by
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
  have hH : sourceSignedResolvent (Complex.exp (-Complex.I*(a:ℂ))) τ B.p B.m s θ=
      (1+signedActualZ a d B ε τ θ)/(1-signedActualZ a d B ε τ θ) := by
    change (1+Complex.exp (-Complex.I*(a:ℂ))*preferredSourceProductPhase τ B.p B.m s θ)/
      (1-Complex.exp (-Complex.I*(a:ℂ))*preferredSourceProductPhase τ B.p B.m s θ)=_
    rw [hZ]
    rfl
  change ‖coordinateJacobian τ B.p B.m s θ*sourceSignedResolvent _ τ B.p B.m s θ‖=_
  rw [hH,coordinateJacobian_eq_shared]
  simp only [preferredCoordinateJacobian,norm_mul,norm_prod,norm_div]
  simp_rw [hinv]
  unfold signedJacobianResolvent
  ring

theorem signed_actual_JH_bound (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ a : ℝ, ∀ N : ℕ, 0<N → ∀ ε τ : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ≤1 → ∀ θ : Fin N → ℝ,
      (∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ‖coordinateJacobian τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ *
        sourceSignedResolvent (Complex.exp (-Complex.I*(a:ℂ))) τ B.p B.m
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        2*C^N*signedJacobianResolvent a d B ε τ θ := by
  obtain ⟨C,hC,hdet⟩ := preferred_contour_determinant_bound d B
  obtain ⟨ε₀,hε₀,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_pos])
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro a N hN ε τ hε hεr hτ hτ1 θ hθ
  obtain ⟨hS,_hSi,hSδ⟩ := hmargin ε hε hεr
  have hZ : ‖signedActualZ a d B ε τ θ‖≤1 := by
    rw [signedActualZ,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,Complex.ofReal_re,
      Complex.neg_im,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,neg_zero,Real.exp_zero,one_mul]
    exact preferredActualZ_norm_le_one d B hε hτ θ
  have hnum : ‖1+signedActualZ a d B ε τ θ‖≤2 := by
    have := norm_add_le (1:ℂ) (signedActualZ a d B ε τ θ)
    rw [norm_one] at this
    linarith
  rw [signed_source_JH_norm_formula a d B hε hτ θ hS hSδ hθ]
  have hnonneg : 0≤signedJacobianResolvent a d B ε τ θ := by
    unfold signedJacobianResolvent
    positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul (hdet N hN τ hτ hτ1 θ) hnum (norm_nonneg _) (by positivity)) hnonneg
  simpa only [mul_comm] using hh

/-- Transfer any scalar estimate to the literal repeatedly transported physical
measure, on its proved open noncollision chart. -/
theorem transportedDensity_bound_of_scalar {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (τ δ : ℝ) (η p m rcut : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hr : ContDiff ℝ ∞ rcut) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (A J : ℝ) (hJ0 : 0≤J)
    (hscalar : ‖(2*Real.pi:ℂ)^(N-1)*regularTransportedScalar τ η p m rcut j s θ‖≤A)
    (hJ : ‖coordinateJacobian τ p m s θ*sourceSignedResolvent σ τ p m s θ‖≤J) :
    ‖(2*Real.pi:ℂ)^(N-1)*transportedDensity σ τ η p m rcut j s θ‖≤J*A := by
  rw [transportedDensity_eq_reconstructed hN σ hσ τ δ η p m rcut hη hp hm hr Ω hΩ hpoint hR j s θ hz,
    reconstructedDensity_eq_source σ τ δ η p m rcut j s θ (hpoint (s,θ) hz)]
  have he : (2*Real.pi:ℂ)^(N-1)*(coordinateJacobian τ p m s θ*
      sourceSignedResolvent σ τ p m s θ*regularTransportedScalar τ η p m rcut j s θ)=
      (coordinateJacobian τ p m s θ*sourceSignedResolvent σ τ p m s θ)*
      ((2*Real.pi:ℂ)^(N-1)*regularTransportedScalar τ η p m rcut j s θ) := by ring
  rw [he,norm_mul]
  exact mul_le_mul hJ hscalar (norm_nonneg _) hJ0

end
end IsingBulk.HT22.Far
