import IsingBulk.AnisoF002.C03.IsotropicCoareaDensityMultiplier
import IsingBulk.AnisoF002.C03.IsotropicIntegratedRightCurrent

/-!
# The actual complete right integral controlled by its coarea measure

The sole total coincidence is ignored only as a Lebesgue null point.
The real cutoff support places the full density in the actual right
rectangle, and the exact complete coarea density bounds its integral.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem norm_integral_actual_right_density_le {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : σ = 1 ∨ σ = -1) (η τ ξ ρ b β B : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hB : 0 ≤ B)
    (g : (Fin (n + 2) → ℝ) → ℂ) (j : ℕ)
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β)
    (hi : Integrable (fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j
      (s, centeredConstraintAngles ρ x)) volume)
    (hbound : ∀ θ ∈ tsupport g, (∃ i l, θ i ≠ θ l) →
      ‖actualTransportedDensity σ η τ ξ g j (s, θ)‖ ≤
        B * actualSignedFullDensity s σ η τ ξ θ) :
    ‖∫ x : Fin (n + 1) → ℝ, actualTransportedDensity σ η τ ξ g j (s, centeredConstraintAngles ρ x)‖ ≤
      B * ∫ x in actualCenteredRightDomain (n + 1) ρ b β,
        actualSignedFullDensity s σ η τ ξ (centeredConstraintAngles ρ x) := by
  let S := actualCenteredRightDomain (n + 1) ρ b β
  let D := fun x : Fin (n + 1) → ℝ => actualTransportedDensity σ η τ ξ g j (s, centeredConstraintAngles ρ x)
  let f := fun x : Fin (n + 1) → ℝ => actualSignedFullDensity s σ η τ ξ (centeredConstraintAngles ρ x)
  have hDzero (x : Fin (n + 1) → ℝ) (hx : x ∉ S) : D x = 0 := by
    by_contra hn
    have hh := actualTransportedDensity_tsupport σ η τ ξ g j (subset_closure hn)
    exact hx (hsupport _ hh)
  have he : (∫ x in S, D x) = ∫ x, D x := setIntegral_eq_integral_of_forall_compl_eq_zero hDzero
  have hf : Continuous f :=
    (actualSignedFullDensity_continuous (by omega) s σ hs hσ η τ ξ hη hτ hξ).comp
      (centeredConstraintAngles_continuous ρ)
  have hfi : IntegrableOn f S volume := hf.continuousOn.integrableOn_compact
    (actualCenteredRightDomain_isCompact _ _ _ _)
  have hI : IntegrableOn D S volume := hi.integrableOn
  have hpoint : ∀ᵐ x ∂volume.restrict S, ‖D x‖ ≤ B * f x := by
    filter_upwards [(Set.countable_singleton (0 : Fin (n + 1) → ℝ)).ae_notMem (volume.restrict S)] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx
    by_cases hsupp : centeredConstraintAngles ρ x ∈ tsupport g
    · exact hbound _ hsupp (centeredConstraintAngles_nonconstant ρ x hx0)
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
