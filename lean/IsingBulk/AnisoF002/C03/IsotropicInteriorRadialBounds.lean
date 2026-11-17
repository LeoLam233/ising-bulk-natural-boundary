import IsingBulk.AnisoF002.C03.IsotropicRadialDifferential
import IsingBulk.AnisoF002.C03.IsotropicTransportDensity

/-!
# Fixed positive radial intervals for the complete current multiplier

Compactness is used only after fixing a positive interior parameter.
It supplies bounded smooth determinant/kernel multipliers at every
coincidence, while the separate retained-power estimates control the
singular covariance velocity and its transported amplitudes.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators ContDiff

theorem compact_radial_multiplier_first_jets {N : ℕ} (hN : 0 < N)
    (α : ℝ) (hα : 0 < α ∧ α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (e₁ e₂ L U : ℝ) (he₁ : 0 < e₁) (he₂ : e₂ ≤ 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε ∈ Icc e₁ e₂, ∀ θ : Fin N → ℝ,
      (∀ i, θ i ∈ Icc L U) →
      ‖actualTransportDensityMultiplier σ η τ ξ (isotropicRadialParameter α ε, θ)‖ ≤ M ∧
      ‖fderiv ℝ (actualTransportDensityMultiplier σ η τ ξ) (isotropicRadialParameter α ε, θ)‖ ≤ M ∧
      ‖fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) (isotropicRadialParameter α ε, θ)‖ ≤ M := by
  let K₀ : Set (ℝ × (Fin N → ℝ)) := Icc e₁ e₂ ×ˢ Icc (fun _ => L) (fun _ => U)
  let φ : ℝ × (Fin N → ℝ) → ℂ × (Fin N → ℝ) :=
    fun p => (isotropicRadialParameter α p.1, p.2)
  have hK₀ : IsCompact K₀ := isCompact_Icc.prod isCompact_Icc
  have hφ : ContinuousOn φ K₀ := by
    intro p hp
    exact (((isotropicRadialParameter_hasDerivAt α p.1 (he₁.trans_le hp.1.1)).continuousAt.comp
      continuousAt_fst).prodMk continuousAt_snd).continuousWithinAt
  have hK : IsCompact (φ '' K₀) := hK₀.image_of_continuousOn hφ
  have hupper : ∀ q ∈ φ '' K₀, 0 < q.1.im := by
    rintro q ⟨p, hp, rfl⟩
    exact (isotropicRadialParameter_estimates α p.1 hα (he₁.trans_le hp.1.1)
      (hp.1.2.trans he₂)).2.2.2.1
  obtain ⟨M, hM, hbound⟩ := compact_interior_multiplier_first_jets hN σ hσ η τ ξ hη hτ hξ
    (φ '' K₀) hK hupper
  refine ⟨M, hM, ?_⟩
  intro ε hε θ hθ
  exact hbound _ ⟨(ε, θ), ⟨hε, ⟨fun i => (hθ i).1, fun i => (hθ i).2⟩⟩, rfl⟩

theorem retained_power_le_uniform {Δ D : ℝ} {k d : ℕ}
    (hΔ : 0 ≤ Δ) (hΔD : Δ ≤ D) (hkd : k ≤ d) :
    Δ ^ k ≤ (max 1 D) ^ d :=
  (pow_le_pow_left₀ hΔ (hΔD.trans (le_max_right _ _)) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) hkd)

/-- Every parameter and angular first jet needed by the actual current
is bounded at fixed positive epsilon; the flux keeps its vanishing
retained degree explicitly. -/
theorem actual_retained_density_local_bounds {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ))
    (A V M Cg Δ D : ℝ) (d : ℕ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hM : 0 ≤ M) (hCg : 0 ≤ Cg) (hΔ : 0 < Δ) (hΔD : Δ ≤ D) (hd : 2 ≤ d)
    (hb : ‖actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j q‖ ≤ A * Cg * Δ ^ d)
    (hnext : ‖actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) (j + 1) q‖ ≤ A * Cg * Δ ^ (d - 2))
    (hdb : ‖fderiv ℝ (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) q‖ ≤ A * (1 + M) * Cg * Δ ^ (d - 1))
    (hv : ∀ i, ‖actualCovarianceAngularVelocity η τ ξ i q‖ ≤ V / Δ)
    (hm : ‖actualTransportDensityMultiplier σ η τ ξ q‖ ≤ M)
    (hdm : ‖fderiv ℝ (actualTransportDensityMultiplier σ η τ ξ) q‖ ≤ M)
    (hbs : DifferentiableAt ℝ (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) q)
    (hms : DifferentiableAt ℝ (actualTransportDensityMultiplier σ η τ ξ) q) :
    ‖actualTransportedDensity σ η τ ξ g j q‖ ≤ M * A * Cg * (max 1 D) ^ d ∧
    ‖actualTransportedDensity σ η τ ξ g (j + 1) q‖ ≤ M * A * Cg * (max 1 D) ^ d ∧
    ‖fderiv ℝ (actualTransportedDensity σ η τ ξ g j) q‖ ≤
      M * (A * (1 + M) * Cg + A * Cg * D) * (max 1 D) ^ d ∧
    ∀ i, ‖actualTransportedFlux σ η τ ξ g j i q‖ ≤ V * M * (A * Cg) * Δ ^ (d - 1) := by
  have hp (k : ℕ) (hk : k ≤ d) := retained_power_le_uniform hΔ.le hΔD hk
  have hD : 0 ≤ D := hΔ.le.trans hΔD
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [actualTransportedDensity, norm_mul]
    exact (mul_le_mul hm hb (norm_nonneg _) hM).trans (by
      calc
        M * (A * Cg * Δ ^ d) ≤ M * (A * Cg * (max 1 D) ^ d) := by
          gcongr
          exact hΔD.trans (le_max_right _ _)
        _ = _ := by ring)
  · simp only [actualTransportedDensity, norm_mul]
    exact (mul_le_mul hm hnext (norm_nonneg _) hM).trans (by
      calc
        M * (A * Cg * Δ ^ (d - 2)) ≤ M * (A * Cg * (max 1 D) ^ d) := by
          gcongr
          exact hp _ (Nat.sub_le _ _)
        _ = _ := by ring)
  · have hh := actualTransportedDensity_first_jet_bound σ η τ ξ g j q (A * Cg)
      (A * (1 + M) * Cg) M Δ D d (by positivity) (by positivity) hM hΔ hΔD
      (by omega) hb hdb hm hdm hbs hms
    exact hh.trans (mul_le_mul_of_nonneg_left (hp _ (Nat.sub_le _ _)) (by positivity))
  · intro i
    exact actualTransportedFlux_retained_bound σ η τ ξ g j i q (A * Cg) V M Δ d
      (by positivity) hV hM hΔ (by omega) hb (hv i) hm

end
end IsingBulk.AnisoF002.Isotropic
