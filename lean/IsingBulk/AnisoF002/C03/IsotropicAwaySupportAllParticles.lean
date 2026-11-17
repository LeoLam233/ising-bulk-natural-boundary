import IsingBulk.AnisoF002.C03.IsotropicPositiveDiameterMajorant
import IsingBulk.AnisoF002.C03.IsotropicPositiveDiameterCoarea

/-!
# Fixed-particle physical derivatives on the positive-diameter complement

Compact angular support supplies its own true positive diameter. The
complete current is differentiated to arbitrary fixed order; its actual
full kernel is integrated by coarea. Every finite particle N≥2 and every
mean/sign is covered on one radius fixed before the cutoff and order.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators ContDiff

theorem exists_actual_all_particle_away_support_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ n : ℕ, ∀ g : (Fin (n + 2) → ℝ) → ℂ, ContDiff ℝ ∞ g →
        (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β) →
        (∀ θ ∈ tsupport g, ∃ i l, θ i ≠ θ l) →
      ∀ j : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ g)
          (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  obtain ⟨βJ, hβJ, hβJ1, hjets⟩ := exists_actual_away_support_coefficient_jets α b hα hb hpoint
  obtain ⟨βV, hβV, _, hvalue⟩ := exists_actual_normalized_cutoff_descendant_buffer α b hα hb hpoint
  obtain ⟨βC, hβC, _, hcoarea⟩ := exists_actual_positive_diameter_coarea_buffer α b hα hb hpoint
  let β := min βJ (min βV βC)
  have hβ : 0 < β := lt_min hβJ (lt_min hβV hβC)
  have hbJ : β ≤ βJ := min_le_left _ _
  have hbV : β ≤ βV := (min_le_right _ _).trans (min_le_left _ _)
  have hbC : β ≤ βC := (min_le_right _ _).trans (min_le_right _ _)
  have hβ1 : β ≤ 1 := hbJ.trans hβJ1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δJ, hδJ, _, hj⟩ := hjets η hη
  obtain ⟨δV, κ, C, M, hδV, _, hκ, hC, hM, hv⟩ := hvalue η hη hwidth
  obtain ⟨δC, hδC, _, hc⟩ := hcoarea η hη hwidth
  obtain ⟨δD, hδD, _, hd⟩ := exists_actual_current_multiplier_coarea_bound η hη
  let δ := min β (min δJ (min δV (min δC δD)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdJ : δ ≤ δJ := (min_le_right _ _).trans (min_le_left _ _)
  have hdV : δ ≤ δV := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC : δ ≤ δC := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdD : δ ≤ δD := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro n g hg hsupport haway j
  have hN : 0 < n + 2 := by omega
  obtain ⟨Cg, hCg, hgjet⟩ := rectangular_cutoff_finite_jet_control hg hsupport j
  obtain ⟨d, hdpos, hgap⟩ := exists_rectangular_cutoff_diameter_gap hN hsupport haway
  obtain ⟨K, hK, hc'⟩ := hc n d hdpos
  obtain ⟨Cj, hCj, hvj⟩ := hv j
  let D := d / Real.sqrt (2 * Real.pi + 4)
  have hD : 0 < D := by dsimp [D]; positivity
  let E := (Cj * ((n + 2 : ℕ) : ℝ) ^ ((7 + 3 * j) * j) * C ^ (n + 2) *
    Real.exp (-κ * ((n + 2 : ℕ) : ℝ) ^ 2 + (1 / 2 : ℝ) * ((n + 2 : ℕ) : ℝ)) * Cg) /
      (((n + 2).factorial : ℝ) * (2 * Real.pi) ^ (n + 2 - 1))
  let B := (2 : ℝ) ^ (n + 2 + 1) * (E / D ^ (2 * j))
  let A := max 1 (B * K)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro σ hσ τ hτ ξ hξ μ ε hε
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have hs := (isotropicRadialParameter_estimates α ε hα hε.1 (hε.2.le.trans hd1)).2.2.2.1
  have hsupp (v : ℝ) (hv : β ≤ v) : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - v) v := by
    intro θ ht k
    have hh := hsupport θ ht k
    exact ⟨by linarith [hh.1], hh.2.trans hv⟩
  obtain ⟨hInt, heq⟩ := hj n g hg (hsupp βJ hbJ) haway σ hσnorm
    τ ⟨hτ.1, hτ.2.trans hdJ⟩ ξ hξ μ j ε ⟨hε.1, hε.2.trans_le hdJ⟩
  rw [heq]
  have hpointbound (θ : Fin (n + 2) → ℝ) (ht : θ ∈ tsupport g) :
      ‖actualTransportedDensity σ η τ ξ g j (isotropicRadialParameter α ε, θ)‖ ≤
        B * actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ θ := by
    obtain ⟨r, hr, hdiam, hlow, _⟩ := exists_actual_diameter_witness hN θ (haway θ ht) 0
    have hΔ := isotropicShellDelta_pos b ε r θ hε.1 hr
    have hDΔ : D ≤ isotropicShellDelta b ε r θ := isotropicShellDelta_diameter_gap hN b β ε r d θ
      hb hβ1 hε.1 (hε.2.le.trans hd1) hr hdpos.le (hgap θ ht r hr.le hdiam) (hsupport θ ht) hlow
    have hv₀ := hvj (n + 2) hN ∅ (Finset.empty_subset _) g Cg hCg.le hg hgjet ε hε.1
      (hε.2.le.trans hdV) τ ξ ⟨hτ.1, hτ.2.trans hdV⟩ hξ θ (hsupp βV hbV θ ht) r hr hdiam hlow
    simp only [Finset.card_empty, mul_zero, pow_zero, mul_one] at hv₀
    have hamp : ‖actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ (fun y => g y.2)) j
        (isotropicRadialParameter α ε, θ)‖ ≤ E / D ^ (2 * j) := by
      apply hv₀.trans
      calc
        _ = E / (isotropicShellDelta b ε r θ) ^ (2 * j) := by dsimp [E]; ring
        _ ≤ _ := div_le_div_of_nonneg_left hE (pow_pos hD _) (pow_le_pow_left₀ hD.le hDΔ _)
    have hmult := hd (n + 2) hN τ ξ ⟨hτ.1, hτ.2.trans hdD⟩ hξ
      (isotropicRadialParameter α ε) σ hs hσnorm θ
    simp only [actualTransportedDensity, norm_mul]
    exact (mul_le_mul hmult hamp (norm_nonneg _) (by
      positivity [actualSignedFullDensity_nonneg (isotropicRadialParameter α ε) σ η τ ξ θ])).trans_eq
      (by dsimp [B]; ring)
  have hpositive (θ : Fin (n + 2) → ℝ) (ht : θ ∈ tsupport g) : ∃ i l, d ≤ θ l - θ i := by
    obtain ⟨r, hr, hdiam, ⟨i, l, hil⟩, _⟩ := exists_actual_diameter_witness hN θ (haway θ ht) 0
    have hh := (hgap θ ht r hr.le hdiam).trans hil
    rcases le_total (θ i) (θ l) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
      exact ⟨i, l, by linarith⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
      exact ⟨l, i, hh⟩
  have hnorm := norm_integral_actual_positive_diameter_density_le _ σ hs hσ η τ ξ μ b βC d B
    hη hτ.1 hξ.1 hB g j (hsupp βC hbC) hpositive hInt hpointbound
  have hco := hc' ε hε.1 (hε.2.le.trans hdC) τ ξ
    ⟨hτ.1, hτ.2.trans hdC⟩ hξ (μ + b) σ hσ
  simp only [add_sub_cancel_right] at hco
  apply hnorm.trans ((mul_le_mul_of_nonneg_left hco hB).trans ?_)
  calc
    _ = (B * K) * (1 + |Real.log ε|) := by ring
    _ ≤ A * (1 + |Real.log ε|) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end
end IsingBulk.AnisoF002.Isotropic
