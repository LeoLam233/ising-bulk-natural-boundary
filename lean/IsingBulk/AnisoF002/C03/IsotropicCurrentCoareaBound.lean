import IsingBulk.AnisoF002.C03.IsotropicRightIntegralMajorant

/-!
# Complete normalized current integrals with their Gaussian coarea bound

All retained factors are taken from the actual full numerator. The
full determinant and product kernel are integrated over the actual
right rectangle. Every fixed mean and either physical sign is covered
by one bound, with the original factorial and angular normalization.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators ContDiff

def rightCurrentCoareaEnvelope (κ C M K Cj Cg : ℝ) (j N m : ℕ) : ℝ :=
  (8 * Cj * (N : ℝ) ^ ((7 + 3 * j) * j + 3) * (2 * C * K) ^ N * M ^ m *
    (max 1 (Real.sqrt (Real.pi + 2))) ^ (2 * m) *
    Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) * Cg) /
    ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1))

theorem exists_actual_current_integral_coarea_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ κ C M K : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧ 1 ≤ K ∧
      ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧
      ∀ (n : ℕ) (R : Finset (Fin (n + 4) × Fin (n + 4))), R ⊆ indexPairs (n + 4) →
        2 * j + 2 ≤ 2 * R.card →
      ∀ (g : (Fin (n + 4) → ℝ) → ℂ) (Cg : ℝ), 0 ≤ Cg → ContDiff ℝ ∞ g →
        FiniteJetControl (j + 1) g Cg → (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ ρ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖∫ x : Fin (n + 3) → ℝ, actualTransportedDensity σ η τ ξ g j
          (isotropicRadialParameter α ε, centeredConstraintAngles ρ x)‖ ≤
          rightCurrentCoareaEnvelope κ C M K Cj Cg j (n + 4) R.card * (1 + |Real.log ε|) := by
  obtain ⟨βV, hβV, hβV1, hvalue⟩ := exists_actual_normalized_cutoff_descendant_buffer α b hα hb hpoint
  obtain ⟨βI, hβI, _, hcurrent⟩ := exists_actual_integrated_right_current_buffer α b hα hb hpoint
  obtain ⟨βC, hβC, _, hcoarea⟩ := exists_actual_full_right_coarea_buffer α b hα hb hpoint
  let β := min βV (min βI βC)
  have hβ : 0 < β := lt_min hβV (lt_min hβI hβC)
  have hbV : β ≤ βV := min_le_left _ _
  have hbI : β ≤ βI := (min_le_right _ _).trans (min_le_left _ _)
  have hbC : β ≤ βC := (min_le_right _ _).trans (min_le_right _ _)
  have hβ1 : β ≤ 1 := hbV.trans hβV1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δV, κ, C, M, hδV, _, hκ, hC, hM, hv⟩ := hvalue η hη hwidth
  obtain ⟨δI, hδI, _, hi⟩ := hcurrent η hη hwidth
  obtain ⟨δC, K, hδC, _, hK, hc⟩ := hcoarea η hη hwidth
  obtain ⟨δD, hδD, _, hd⟩ := exists_actual_current_multiplier_coarea_bound η hη
  let δ := min β (min δV (min δI (min δC δD)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdV : δ ≤ δV := (min_le_right _ _).trans (min_le_left _ _)
  have hdI : δ ≤ δI := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC : δ ≤ δC := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdD : δ ≤ δD := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hd1 : δ ≤ 1 := hdβ.trans hβ1
  refine ⟨δ, κ, C, M, K, hδ, hdβ, hκ, hC, hM, hK, ?_⟩
  intro j
  obtain ⟨Cj, hCj, hvj⟩ := hv j
  refine ⟨Cj, hCj, ?_⟩
  intro n R hR hj g Cg hCg hg hgj hsupport σ hσ τ hτ ξ hξ ρ ε hε
  have hN : 0 < n + 4 := by omega
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have hs := (isotropicRadialParameter_estimates α ε hα hε.1 (hε.2.le.trans hd1)).2.2.2.1
  have hsuppI : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - βI) βI := by
    intro θ ht k
    have hh := hsupport θ ht k
    exact ⟨by linarith [hh.1], hh.2.trans hbI⟩
  have hsuppC : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - βC) βC := by
    intro θ ht k
    have hh := hsupport θ ht k
    exact ⟨by linarith [hh.1], hh.2.trans hbC⟩
  have hInt := (hi (n + 2) R hR j hj g Cg hCg hg hgj hsuppI σ hσnorm
    τ ⟨hτ.1, hτ.2.trans hdI⟩ ξ hξ ρ ε ⟨hε.1, hε.2.trans_le hdI⟩).1
  let L := (Cj * (n + 4 : ℕ) ^ ((7 + 3 * j) * j) * C ^ (n + 4) * M ^ R.card *
    Real.exp (-κ * ((n + 4 : ℕ) : ℝ) ^ 2 + (1 / 2 : ℝ) * (n + 4)) * Cg) /
    (((n + 4).factorial : ℝ) * (2 * Real.pi) ^ ((n + 4) - 1))
  let B := (2 : ℝ) ^ ((n + 4) + 1) * L * (max 1 (Real.sqrt (Real.pi + 2))) ^ (2 * R.card)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpointbound (θ : Fin (n + 4) → ℝ) (ht : θ ∈ tsupport g) (hne : ∃ i l, θ i ≠ θ l) :
      ‖actualTransportedDensity σ η τ ξ g j (isotropicRadialParameter α ε, θ)‖ ≤
        B * actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ θ := by
    have hθ := hsupport θ ht
    have hθV : ∀ k, θ k ∈ Icc (-b - βV) βV :=
      fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hbV⟩
    obtain ⟨r, hr, hdiam, hlow, _⟩ := exists_actual_diameter_witness hN θ hne 0
    have hv₀ := hvj (n + 4) hN R hR g Cg hCg hg (hgj.mono_order (by omega)) ε hε.1
      (hε.2.le.trans hdV) τ ξ ⟨hτ.1, hτ.2.trans hdV⟩ hξ θ hθV r hr hdiam hlow
    have hΔ := isotropicShellDelta_pos b ε r θ hε.1 hr
    have hΔD := isotropicShellDelta_right_uniform b β ε r θ hb.2 hβ1 hε.1 hr hθ hlow
    have hpower := retained_power_uniform_bound hΔ hΔD (show 2 * j ≤ 2 * R.card by omega)
    have hamp : ‖actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ (fun y => g y.2)) j
        (isotropicRadialParameter α ε, θ)‖ ≤ L * (max 1 (Real.sqrt (Real.pi + 2))) ^ (2 * R.card) := by
      apply hv₀.trans
      calc
        _ = L * ((isotropicShellDelta b ε r θ) ^ (2 * R.card) /
          (isotropicShellDelta b ε r θ) ^ (2 * j)) := by dsimp [L]; push_cast; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpower hL
    have hmult := hd (n + 4) hN τ ξ ⟨hτ.1, hτ.2.trans hdD⟩ hξ
      (isotropicRadialParameter α ε) σ hs hσnorm θ
    simp only [actualTransportedDensity, norm_mul]
    exact (mul_le_mul hmult hamp (norm_nonneg _) (by
      positivity [actualSignedFullDensity_nonneg (isotropicRadialParameter α ε) σ η τ ξ θ])).trans_eq
      (by dsimp [B]; ring)
  have hnorm := norm_integral_actual_right_density_le _ σ hs hσ η τ ξ ρ b βC B
    hη hτ.1 hξ.1 hB g j hsuppC hInt hpointbound
  have hco := hc n ε hε.1 (hε.2.le.trans hdC) τ ξ
    ⟨hτ.1, hτ.2.trans hdC⟩ hξ (ρ + b) σ hσ
  simp only [add_sub_cancel_right] at hco
  apply hnorm.trans ((mul_le_mul_of_nonneg_left hco hB).trans_eq ?_)
  dsimp [B, L, rightCurrentCoareaEnvelope]
  simp only [pow_add, mul_pow]
  push_cast
  ring

end
end IsingBulk.AnisoF002.Isotropic
