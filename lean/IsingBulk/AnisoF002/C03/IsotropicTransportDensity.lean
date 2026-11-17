import IsingBulk.AnisoF002.C03.IsotropicParameterHolomorphy
import IsingBulk.AnisoF002.C03.IsotropicTransportSupport
import IsingBulk.AnisoF002.C03.IsotropicCoincidenceExtension

/-!
# Literal complete transported densities and their retained powers

These abbreviations keep the original physical determinant, signed
product kernel, complete normalized initial numerator and full cutoff
transport recurrence. The support and current bounds apply to exactly
that density; no particle factor is discarded.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

variable {N : ℕ}

def actualTransportedDensity (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  actualTransportDensityMultiplier σ η τ ξ q *
    actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ (fun y => g y.2)) j q

def actualTransportedFlux (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  actualCovarianceAngularVelocity η τ ξ i q * actualTransportedDensity σ η τ ξ g j q

theorem actualTransportedDensity_tsupport (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) :
    tsupport (actualTransportedDensity σ η τ ξ g j) ⊆ Prod.snd ⁻¹' tsupport g :=
  tsupport_mul_subset_right.trans (actualTransportDescendant_cutoff_tsupport η τ ξ g j)

theorem actualTransportedFlux_tsupport (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) :
    tsupport (actualTransportedFlux σ η τ ξ g j i) ⊆ Prod.snd ⁻¹' tsupport g :=
  tsupport_mul_subset_right.trans (actualTransportedDensity_tsupport σ η τ ξ g j)

theorem actualTransportedDensity_zero_germ (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    actualTransportedDensity σ η τ ξ g j =ᶠ[𝓝 q] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (actualTransportedDensity_tsupport σ η τ ξ g j h))

theorem actualTransportedFlux_zero_germ (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N)
    (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    actualTransportedFlux σ η τ ξ g j i =ᶠ[𝓝 q] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (actualTransportedFlux_tsupport σ η τ ξ g j i h))

theorem fderiv_product_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℂ) (x : E) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hg]
  exact (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_smul _ _))
    (le_of_eq (norm_smul _ _)))

/-- The full flux loses exactly one retained shell power. -/
theorem actualTransportedFlux_retained_bound (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (i : Fin N) (q : ℂ × (Fin N → ℝ))
    (A V M Δ : ℝ) (d : ℕ) (_hA : 0 ≤ A) (hV : 0 ≤ V) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hd : 1 ≤ d)
    (hb : ‖actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j q‖ ≤ A * Δ ^ d)
    (hv : ‖actualCovarianceAngularVelocity η τ ξ i q‖ ≤ V / Δ)
    (hm : ‖actualTransportDensityMultiplier σ η τ ξ q‖ ≤ M) :
    ‖actualTransportedFlux σ η τ ξ g j i q‖ ≤ V * M * A * Δ ^ (d - 1) := by
  simp only [actualTransportedFlux, actualTransportedDensity, norm_mul]
  calc
    _ ≤ (V / Δ) * (M * (A * Δ ^ d)) := by gcongr
    _ = V * M * A * (Δ ^ d / Δ) := by ring
    _ = _ := by
      have he : Δ ^ d / Δ = Δ ^ (d - 1) := by
        simpa only [pow_one] using retained_power_division hΔ.ne' hd
      rw [he]

/-- The genuine first real jet of the complete density retains the
smaller of the amplitude value and first-jet degrees. -/
theorem actualTransportedDensity_first_jet_bound (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ))
    (A B M Δ D : ℝ) (d : ℕ) (hA : 0 ≤ A) (_hB : 0 ≤ B) (hM : 0 ≤ M)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D) (hd : 1 ≤ d)
    (hb : ‖actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j q‖ ≤ A * Δ ^ d)
    (hdb : ‖fderiv ℝ (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) q‖ ≤ B * Δ ^ (d - 1))
    (hm : ‖actualTransportDensityMultiplier σ η τ ξ q‖ ≤ M)
    (hdm : ‖fderiv ℝ (actualTransportDensityMultiplier σ η τ ξ) q‖ ≤ M)
    (hbs : DifferentiableAt ℝ (actualTransportDescendant η τ ξ
      (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) q)
    (hms : DifferentiableAt ℝ (actualTransportDensityMultiplier σ η τ ξ) q) :
    ‖fderiv ℝ (actualTransportedDensity σ η τ ξ g j) q‖ ≤
      M * (B + A * D) * Δ ^ (d - 1) := by
  apply (fderiv_product_norm_le _ _ q hms hbs).trans
  calc
    _ ≤ M * (B * Δ ^ (d - 1)) + (A * Δ ^ d) * M := by gcongr
    _ = M * (B + A * Δ) * Δ ^ (d - 1) := by
      have he : Δ ^ d = Δ ^ (d - 1) * Δ := by
        calc
          Δ ^ d = Δ ^ ((d - 1) + 1) := by congr 1; omega
          _ = _ := pow_succ _ _
      rw [he]
      ring
    _ ≤ _ := by gcongr

end
end IsingBulk.AnisoF002.Isotropic
