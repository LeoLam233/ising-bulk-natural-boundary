import IsingBulk.AnisoF002.C03.IsotropicAnalyticDescendantPullback

/-!
# Complete normalized real-frame descendants before smooth localization

The original normalized numerator enters the actual current recurrence.
Its complete descendants satisfy the frozen retained-degree estimates on
every actual right shell. All analytic and inverse-coordinate premises
are discharged from the constructed physical neighborhood.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem isotropicParticleNormalization_norm (N : ℕ) :
    ‖isotropicParticleNormalization N‖ =
      1 / ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1)) := by
  simp only [isotropicParticleNormalization, norm_inv, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem exists_actual_normalized_unweighted_descendant_bound (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i l, |θ i - θ l| ≤ 2 * r) → (∃ i l, r ≤ |θ i - θ l|) →
        let Δ := isotropicShellDelta b ε r θ
        ‖actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ (fun _ => 1)) j
          (isotropicRadialParameter α ε, θ)‖ ≤
          (Cj * (N : ℝ) ^ (5 * j) * C ^ N * M ^ R.card *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) *
              Δ ^ (2 * R.card) / Δ ^ (2 * j)) /
            ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1)) := by
  obtain ⟨δA, κ, C, M, c, B, hδA, hδA1, hκ, hC, hM, hc, hB, hballs⟩ :=
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
  obtain ⟨δD, hδD, hdata⟩ := exists_actual_right_current_data (2 * Real.cos α) η hS hη
  let δ := min δA (δD / 8)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA' : δ ≤ δA := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδA'.trans hδA1
  have hδD8 : δ ≤ δD / 8 := min_le_right _ _
  have hδD' : δ ≤ δD := by linarith only [hδD8, hδD]
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨δ, κ, C, M, hδ, hδ1, hκ, hC, hM, ?_⟩
  intro j
  refine ⟨scaledTransportJetConstant j 0 c B D₀,
    scaledTransportJetConstant_pos j 0 c B D₀ hc hB hD₀, ?_⟩
  intro N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let s := isotropicRadialParameter α ε
  let x := (s, θ)
  let q := actualHomotopyRegularTuple s η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  let F : RegularJointSpace N → ℂ := fun p => isotropicParticleNormalization N * completeRegularNumerator N p
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  obtain ⟨hΔD, hball⟩ := hballs N hN R hR ε hε (hεδ.trans hδA') τ ξ
    ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
    (fun i => ⟨by linarith only [(hθ i).1, hδA'], (hθ i).2.trans hδA'⟩)
    r hr hdiam hdiamLower
  have hqball : q ∈ ball q (c * Δ / (N : ℝ) ^ 2) := mem_ball_self (by positivity)
  have hFball : AnalyticOnNhd ℂ F (ball q (c * Δ / (N : ℝ) ^ 2)) :=
    fun p hp => analyticAt_const.mul (hball p hp).2.2.1
  have hFbound : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤
      (‖isotropicParticleNormalization N‖ * C ^ N * M ^ R.card *
        Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) * Δ ^ (2 * R.card) := by
    intro p hp
    change ‖isotropicParticleNormalization N * completeRegularNumerator N p‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hball p hp).2.2.2 (norm_nonneg _)).trans_eq (by ring)
  have hbound := analyticTransportDescendant_scaled_joint_jets hN
    (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) F q c B D₀ Δ
    (‖isotropicParticleNormalization N‖ * C ^ N * M ^ R.card *
      Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) (2 * R.card) j 0
    hc hB hD₀ hΔ hΔD (by positivity) (fun p hp => (hball p hp).1) hFball
    (fun p hp => (hball p hp).2.1) hFbound
  rw [norm_iteratedFDeriv_zero] at hbound
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist s ((2 * Real.cos α : ℝ) : ℂ) < δD :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδD8, hδD])
  obtain ⟨i, l, hil⟩ := hdiamLower
  have hneq : θ i ≠ θ l := by intro he; rw [he, sub_self, abs_zero] at hil; linarith only [hil, hr]
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δD) δD := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδD'], (hθ i).2.trans hδD'⟩
  obtain ⟨hχ, hdet, _⟩ := hdata N hN s hrad.2.2.2.1 hsnear τ
    ⟨hτ.1, hτ.2.trans hδD'⟩ ξ hξ θ hθD i l hneq
  have he := regularTransportDescendant_joint_pullback (actualPhysicalCoordinate η τ ξ)
    (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) F x hχ
    (hball q hqball).1 (hFball q hqball) hdet j
  change regularTransportDescendant (actualPhysicalCoordinate η τ ξ)
    actualAngularDirection actualTimeDirection (actualCovarianceRegularField η τ ξ)
    (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) j x =
      analyticTransportDescendant (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) F j q at he
  have hinit : actualInitialAmplitude η τ ξ (fun _ : ℂ × (Fin N → ℝ) => 1) =
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y)) := by
    funext y
    simp only [actualInitialAmplitude, mul_one, actualRegularNumerator, F, regularJointMap]
  rw [actualTransportDescendant, hinit, he]
  exact hbound.trans_eq (by
    simp only [isotropicParticleNormalization_norm, mul_zero, add_zero]
    ring)

end IsingBulk.AnisoF002.Isotropic
