import IsingBulk.AnisoF002.C03.IsotropicCutoffCoefficient

/-!
# A common actual shell ball for every analytic transport branch

The full numerator, covariance field, and the inverse-coordinate slope
coefficient controlling differentiated real cutoffs all use one ball.
Its constants and physical neighborhood are fixed before particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_actual_complete_cutoff_transport_balls (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ κ C M c B K : ℝ,
      0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧ 0 < c ∧ 0 < B ∧ 0 < K ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) → (∃ i j, r ≤ |θ i - θ j|) →
        let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
        let Δ := isotropicShellDelta b ε r θ
        Δ ≤ Real.sqrt (Real.pi + 2) ∧
        ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2),
          AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) p ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ B * (N : ℝ) ^ 2 / Δ ∧
          AnalyticAt ℂ (completeRegularNumerator N) p ∧
          ‖completeRegularNumerator N p‖ ≤
            C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) *
              Δ ^ (2 * R.card) ∧
          ∀ j : Fin N, AnalyticAt ℂ (fun z => rightCutoffTransportCoefficient z j) p ∧
            ‖rightCutoffTransportCoefficient p j‖ ≤ K * (N : ℝ) ^ 2 / Δ := by
  obtain ⟨δA, κ, C, M, cA, B, hδA, hδA1, hκ, hC, hM, hcA, hB, hball⟩ :=
    exists_actual_complete_transport_balls α b η hα hb hpoint hη hwidth
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  have hbS : rightBranchEndpoint (2 * Real.cos α) = b := by
    unfold rightBranchEndpoint
    rw [show 2 * Real.cos α - 1 = Real.cos b by linarith only [hpoint]]
    exact Real.arccos_cos hb.1.le hb.2.le
  obtain ⟨RU, CU, hRU, hCU, hU⟩ := exists_right_inverse_first_slope_control (2 * Real.cos α) hS
  obtain ⟨δU, hδU, hdomain⟩ := exists_actual_right_homotopy_domain
    (2 * Real.cos α) (RU / 2) hS (half_pos hRU)
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  let δ := min δA (δU / 8)
  let c := min cA (RU / (2 * D₀))
  let K := CU * (D₀ + B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA' : δ ≤ δA := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδA'.trans hδA1
  have hδU8 : δ ≤ δU / 8 := min_le_right _ _
  have hδU' : δ ≤ δU := by linarith only [hδU8, hδU]
  have hc : 0 < c := by dsimp [c]; positivity
  have hcA' : c ≤ cA := min_le_left _ _
  have hcRU : c * D₀ ≤ RU / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D₀ by positivity)).mp
      (show c ≤ RU / (2 * D₀) from min_le_right _ _)
    nlinarith only [hh]
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨δ, κ, C, M, c, B, K, hδ, hδ1, hκ, hC, hM, hc, hB, hK, ?_⟩
  intro N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hΔD, hballA⟩ := hball N hN R hR ε hε (hεδ.trans hδA') τ ξ
    ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
    (fun i => ⟨by linarith only [(hθ i).1, hδA'], (hθ i).2.trans hδA'⟩)
    r hr hdiam hdiamLower
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δU :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδU8, hδU])
  have hθU : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δU) δU := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδU'], (hθ i).2.trans hδU'⟩
  have hqU : q ∈ rightProductDomain (2 * Real.cos α) (RU / 2) N :=
    (hdomain N hN _ hrad.2.2.2.1 hsnear η τ ξ hη
      ⟨hτ.1, hτ.2.trans hδU'⟩ hξ θ hθU).1
  have hρU : c * Δ / (N : ℝ) ^ 2 ≤ RU / 2 :=
    (div_le_self (mul_nonneg hc.le hΔ.le) (one_le_pow₀ hN1)).trans
      ((mul_le_mul_of_nonneg_left hΔD hc.le).trans hcRU)
  refine ⟨hΔD, ?_⟩
  intro p hp
  have hpA : p ∈ ball q (cA * Δ / (N : ℝ) ^ 2) :=
    ball_subset_ball (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcA' hΔ.le)
      (by positivity)) hp
  have hpU : p ∈ rightProductDomain (2 * Real.cos α) RU N :=
    rightProductDomain_half_ball_subset _ _ _ q hqU (ball_subset_ball hρU hp)
  have hA := hballA p hpA
  refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  intro j
  have hUj := hU N p hpU j
  refine ⟨rightCutoffTransportCoefficient_analyticAt p j hUj.1 hA.1, ?_⟩
  have hscale : 1 + B * (N : ℝ) ^ 2 / Δ ≤ (D₀ + B) * (N : ℝ) ^ 2 / Δ := by
    have hh : (1 : ℝ) ≤ D₀ * (N : ℝ) ^ 2 / Δ := by
      apply (le_div_iff₀ hΔ).mpr
      simpa only [one_mul] using
        hΔD.trans (le_mul_of_one_le_right hD₀.le (one_le_pow₀ hN1))
    calc
      _ ≤ D₀ * (N : ℝ) ^ 2 / Δ + B * (N : ℝ) ^ 2 / Δ := add_le_add hh le_rfl
      _ = _ := by ring
  exact (rightCutoffTransportCoefficient_norm_le p j CU (B * (N : ℝ) ^ 2 / Δ)
    hCU.le hUj.1.differentiableAt hUj.2 hA.2.1).trans
      ((mul_le_mul_of_nonneg_left hscale hCU.le).trans_eq (by dsimp [K]; ring))

end IsingBulk.AnisoF002.Isotropic
