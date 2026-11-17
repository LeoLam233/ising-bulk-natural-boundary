import IsingBulk.AnisoF002.C03.IsotropicRightShellCover

/-!
# Summing the actual dyadic coarea integrals

The countable cover is integrated before any particle sum. Positivity,
ordinary Lebesgue measure and the proved geometric shell estimate give
one bound on the entire fixed-mean right rectangle, including every
partial coincidence and both physical signs.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric MeasureTheory

theorem integral_countable_union_nonneg_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : ℕ → Set X) (f : X → ℝ) (A : ℕ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hI : ∀ k, IntegrableOn f (S k) μ)
    (hA : Summable A) (hA0 : ∀ k, 0 ≤ A k)
    (hbound : ∀ k, (∫ x in S k, f x ∂μ) ≤ A k) :
    IntegrableOn f (⋃ k, S k) μ ∧ (∫ x in ⋃ k, S k, f x ∂μ) ≤ ∑' k, A k := by
  have hs : Summable (fun k => ∫ x in S k, f x ∂μ) :=
    hA.of_nonneg_of_le (fun _ => integral_nonneg hf) hbound
  have hn : Summable (fun k => ∫ x in S k, ‖f x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hf _)] using hs
  have hU := integrableOn_iUnion_of_summable_integral_norm hI hn
  refine ⟨hU, ?_⟩
  have hh := lintegral_iUnion_le (μ := μ) S (fun x => ENNReal.ofReal (f x))
  have he (k : ℕ) : (∫⁻ x in S k, ENNReal.ofReal (f x) ∂μ) =
      ENNReal.ofReal (∫ x in S k, f x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hI k) (Eventually.of_forall hf)).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hU (Eventually.of_forall hf)] at hh
  simp_rw [he] at hh
  have ht : (∑' k, ENNReal.ofReal (∫ x in S k, f x ∂μ)) ≤ ENNReal.ofReal (∑' k, A k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hA0 hA]
    exact ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hbound k))
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hA0)).mp (hh.trans ht)

theorem actualSignedFullDensity_continuous {N : ℕ} (hN : 0 < N) (s σ : ℂ)
    (hs : 0 < s.im) (hσ : σ = 1 ∨ σ = -1) (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    Continuous (actualSignedFullDensity (N := N) s σ η τ ξ) := by
  rcases hσ with rfl | rfl
  · rw [show actualSignedFullDensity (N := N) s 1 η τ ξ = actualFullPhaseDensity s η τ ξ 0
      from funext (fun θ => (actualFullPhaseDensity_zero_eq_signed s η τ ξ θ).symm)]
    exact actualFullPhaseDensity_angles_continuous s hs η τ ξ 0 hη hτ hξ ⟨0, hN⟩
  · rw [show actualSignedFullDensity (N := N) s (-1) η τ ξ = actualFullPhaseDensity s η τ ξ Real.pi
      from funext (fun θ => (actualFullPhaseDensity_pi_eq_signed s η τ ξ θ).symm)]
    exact actualFullPhaseDensity_angles_continuous s hs η τ ξ Real.pi hη hτ hξ ⟨0, hN⟩

theorem actualSignedFullDensity_nonneg {N : ℕ} (s σ : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    0 ≤ actualSignedFullDensity s σ η τ ξ θ := by
  unfold actualSignedFullDensity
  positivity

/-- The complete fixed-mean right integral, with one constant before
all N >= 4, every positive radial depth and both physical signs. -/
theorem exists_actual_full_right_coarea (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ : ℝ,
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredRightDomain (n + 3) (μ - b) b δ,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          4 * K ^ (n + 4) * (n + 4) ^ 3 * (1 + |Real.log ε|) := by
  obtain ⟨δ, K, hδ, hδ1, hK1, hbound⟩ :=
    exists_actual_signed_shell_delta_bound α b η hα hb hpoint hη hwidth
  let R := b + 2 * δ
  let L := max 1 (Real.sqrt R)
  have hR : 0 < R := by dsimp [R]; linarith only [hb.1, hδ]
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hK : 0 < K := zero_lt_one.trans_le hK1
  refine ⟨δ, K * L, hδ, hδ1, one_le_mul_of_one_le_of_one_le hK1 hL1, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ σ hσ
  let f : (Fin (n + 3) → ℝ) → ℝ := fun x =>
    actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ (centeredConstraintAngles (μ - b) x)
  let S : ℕ → Set (Fin (n + 3) → ℝ) := fun k =>
    actualCenteredShell (n + 3) (μ - b) b δ (dyadicRadius R k)
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
  have hcover : actualCenteredRightDomain (n + 3) (μ - b) b δ ≤ᵐ[volume] ⋃ k, S k := by
    filter_upwards [(countable_singleton (0 : Fin (n + 3) → ℝ)).ae_notMem volume] with x hx0
    intro hx
    exact (actualCenteredRightDomain_subset_shells (μ - b) b δ hb.1 hδ.le hx).resolve_left hx0
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
