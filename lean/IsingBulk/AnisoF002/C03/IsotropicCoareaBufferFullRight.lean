import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferShellScale
import IsingBulk.AnisoF002.C03.IsotropicCountableCoarea

/-!
# Actual countable shell summation on the preselected full right rectangle
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_full_right_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ K : ℝ, 0 < δ ∧ δ ≤ β ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ : ℝ,
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredRightDomain (n + 3) (μ - b) b β,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          4 * K ^ (n + 4) * (n + 4) ^ 3 * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_signed_shell_delta_bound_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, K, hδ, hδβ, hK1, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  let R := b + 2 * β
  let L := max 1 (Real.sqrt R)
  have hR : 0 < R := by dsimp [R]; linarith only [hb.1, hβ]
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hK : 0 < K := zero_lt_one.trans_le hK1
  refine ⟨δ, K * L, hδ, hδβ, one_le_mul_of_one_le_of_one_le hK1 hL1, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ σ hσ
  let f : (Fin (n + 3) → ℝ) → ℝ := fun x =>
    actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ (centeredConstraintAngles (μ - b) x)
  let S : ℕ → Set (Fin (n + 3) → ℝ) := fun k =>
    actualCenteredShell (n + 3) (μ - b) b β (dyadicRadius R k)
  let A : ℕ → ℝ := fun k => K ^ (n + 4) * (n + 4) ^ 3 *
    shellDelta μ ε (dyadicRadius R k) ^ (n + 1) * (1 + |Real.log ε|)
  have hs : 0 < (isotropicRadialParameter α ε).im :=
    (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hf : Continuous f :=
    (actualSignedFullDensity_continuous (by omega) _ σ hs hσ η τ ξ hη hτ.1 hξ.1).comp
      (centeredConstraintAngles_continuous (μ - b))
  have hf0 (x) : 0 ≤ f x := actualSignedFullDensity_nonneg _ _ _ _ _ _
  have hI (k) : IntegrableOn f (S k) volume := hf.continuousOn.integrableOn_compact
    (actualCenteredShell_isCompact _ _ _ _ _)
  have hseries := shellDelta_dyadic_summable_bound μ ε R hε hR n
  have hA : Summable A := (hseries.1.mul_left (K ^ (n + 4) * (n + 4) ^ 3)).mul_right
    (1 + |Real.log ε|)
  have hA0 (k) : 0 ≤ A k := by
    dsimp [A]
    positivity [shellDelta_pos μ ε (dyadicRadius R k) hε (dyadicRadius_pos R hR k)]
  have hB (k) : (∫ x in S k, f x) ≤ A k := by
    have hh := hbound (n + 1) ε hε hεδ τ ξ hτ hξ μ (dyadicRadius R k)
      (dyadicRadius_pos R hR k) σ hσ
    convert hh using 1
    simp only [A, shellDelta, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨hU, hsum⟩ := integral_countable_union_nonneg_le volume S f A hf0 hI hA hA0 hB
  have hcover : actualCenteredRightDomain (n + 3) (μ - b) b β ≤ᵐ[volume] ⋃ k, S k := by
    filter_upwards [(countable_singleton (0 : Fin (n + 3) → ℝ)).ae_notMem volume] with x hx0
    intro hx
    exact (actualCenteredRightDomain_subset_shells (μ - b) b β hb.1 hβ.le hx).resolve_left hx0
  have hright := (setIntegral_mono_set hU (Eventually.of_forall hf0) hcover).trans hsum
  have he : (∑' k, A k) = (K ^ (n + 4) * (n + 4) ^ 3) *
      (∑' k, shellDelta μ ε (dyadicRadius R k) ^ (n + 1)) * (1 + |Real.log ε|) := by
    simp only [A, tsum_mul_left, tsum_mul_right]
  rw [he] at hright
  have hscale : shellDelta μ ε R ^ (n + 1) ≤ L ^ (n + 4) := by
    calc
      _ ≤ L ^ (n + 1) := pow_le_pow_left₀ (shellDelta_pos μ ε R hε hR).le
        ((shellDelta_le_sqrt_radius μ ε R hε hR).trans (le_max_right _ _)) _
      _ ≤ L ^ (n + 4) := pow_le_pow_right₀ hL1 (by omega)
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hseries.2 (by positivity : 0 ≤ K ^ (n + 4) * (n + 4) ^ 3))
    (by positivity : 0 ≤ 1 + |Real.log ε|)
  have hbnd2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 4))
      (by positivity : 0 ≤ K ^ (n + 4) * (n + 4) ^ 3))
    (by positivity : 0 ≤ 1 + |Real.log ε|)
  exact (hright.trans hbnd).trans (hbnd2.trans_eq (by rw [mul_pow]; ring))

end IsingBulk.AnisoF002.Isotropic
