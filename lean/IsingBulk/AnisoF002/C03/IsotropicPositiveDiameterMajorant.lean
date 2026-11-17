import IsingBulk.AnisoF002.C03.IsotropicCutoffDiameterGap
import IsingBulk.AnisoF002.C03.IsotropicPositiveDiameterGeometry
import IsingBulk.AnisoF002.C03.IsotropicCoareaDensityMultiplier

/-!
# The full current integral on its actual positive-diameter support
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem norm_integral_actual_positive_diameter_density_le {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : σ = 1 ∨ σ = -1) (η τ ξ ρ b β d B : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hB : 0 ≤ B)
    (g : (Fin (n + 2) → ℝ) → ℂ) (j : ℕ)
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β)
    (hpositive : ∀ θ ∈ tsupport g, ∃ i l, d ≤ θ l - θ i)
    (hi : Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j
      (s, centeredConstraintAngles ρ x)))
    (hbound : ∀ θ ∈ tsupport g, ‖actualTransportedDensity σ η τ ξ g j (s, θ)‖ ≤
      B * actualSignedFullDensity s σ η τ ξ θ) :
    ‖∫ x : Fin (n + 1) → ℝ, actualTransportedDensity σ η τ ξ g j (s, centeredConstraintAngles ρ x)‖ ≤
      B * ∫ x in actualPositiveDiameterDomain (n + 1) ρ b β d,
        actualSignedFullDensity s σ η τ ξ (centeredConstraintAngles ρ x) := by
  let S := actualPositiveDiameterDomain (n + 1) ρ b β d
  let D := fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j (s, centeredConstraintAngles ρ x)
  let f := fun x : Fin (n + 1) → ℝ => actualSignedFullDensity s σ η τ ξ (centeredConstraintAngles ρ x)
  have hDzero (x : Fin (n + 1) → ℝ) (hx : x ∉ S) : D x = 0 := by
    by_contra hn
    have hh := actualTransportedDensity_tsupport σ η τ ξ g j (subset_closure hn)
    exact hx ⟨hsupport _ hh, hpositive _ hh⟩
  have he : (∫ x in S, D x) = ∫ x, D x := setIntegral_eq_integral_of_forall_compl_eq_zero hDzero
  have hf : Continuous f :=
    (actualSignedFullDensity_continuous (by omega) s σ hs hσ η τ ξ hη hτ hξ).comp
      (centeredConstraintAngles_continuous ρ)
  have hfi : IntegrableOn f S volume := hf.continuousOn.integrableOn_compact
    (actualPositiveDiameterDomain_isCompact _ _ _ _ _)
  have hI : IntegrableOn D S volume := hi.integrableOn
  have hpoint : ∀ᵐ x ∂volume.restrict S, ‖D x‖ ≤ B * f x := by
    exact Eventually.of_forall fun x => by
      by_cases hsupp : centeredConstraintAngles ρ x ∈ tsupport g
      · exact hbound _ hsupp
      · have hz := (actualTransportedDensity_zero_germ σ η τ ξ g j
          (s, centeredConstraintAngles ρ x) hsupp).eq_of_nhds
        change ‖actualTransportedDensity σ η τ ξ g j _‖ ≤ _
        rw [hz, norm_zero]
        exact mul_nonneg hB (actualSignedFullDensity_nonneg _ _ _ _ _ _)
  change ‖∫ x, D x‖ ≤ B * ∫ x in S, f x
  rw [← he]
  exact (norm_integral_le_integral_norm D).trans
    ((integral_mono_ae hI.norm (hfi.const_mul B) hpoint).trans_eq (integral_const_mul B f))

end
end IsingBulk.AnisoF002.Isotropic
