import IsingBulk.AnisoF002.C03.IsotropicInitialAmplitude
import IsingBulk.AnisoF002.C03.IsotropicActualCovarianceJets

/-!
# Complete initial numerator jets with the full retained collision degree

A complex ball of radius proportional to the frozen shell scale preserves
all retained differences at that scale. The existing complete Gaussian
quotient estimate applies on the same ball. Cauchy's inequality then
retains degree D-s for every joint derivative of order s, including
parameter derivatives, without differentiating the scale or discarding
any factor of the original complete numerator.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric

theorem retainedCollisionPolynomial_norm_bound {N : ℕ} (R : Finset (Fin N × Fin N))
    (v : Fin N → ℂ) (A Δ : ℝ)
    (hv : ∀ ij ∈ R, ‖v ij.1 - v ij.2‖ ≤ A * Δ) :
    ‖retainedCollisionPolynomial R v‖ ≤ A ^ (2 * R.card) * Δ ^ (2 * R.card) := by
  rw [retainedCollisionPolynomial, norm_prod]
  calc
    (∏ ij ∈ R, ‖(v ij.1 - v ij.2) ^ 2‖) ≤ ∏ _ij ∈ R, (A * Δ) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro ij hij
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hv ij hij) _
    _ = A ^ (2 * R.card) * Δ ^ (2 * R.card) := by
      rw [Finset.prod_const, ← pow_mul, mul_pow]

theorem coordinate_differences_on_scaled_ball {N : ℕ} (q : ℂ × (Fin N → ℂ))
    (A Δ ρ : ℝ) (hρ : ρ ≤ Δ) (hq : ∀ i j, ‖q.2 i - q.2 j‖ ≤ A * Δ)
    (p : ℂ × (Fin N → ℂ)) (hp : p ∈ ball q ρ) :
    ∀ i j, ‖p.2 i - p.2 j‖ ≤ (A + 2) * Δ := by
  have hdist : dist p.2 q.2 < ρ := by
    have hh : dist p.1 q.1 < ρ ∧ dist p.2 q.2 < ρ := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hp
    exact hh.2
  intro i j
  have hi : ‖p.2 i - q.2 i‖ ≤ Δ := by
    rw [← dist_eq_norm]
    exact (dist_le_pi_dist p.2 q.2 i).trans (hdist.le.trans hρ)
  have hj : ‖p.2 j - q.2 j‖ ≤ Δ := by
    rw [← dist_eq_norm]
    exact (dist_le_pi_dist p.2 q.2 j).trans (hdist.le.trans hρ)
  have he : p.2 i - p.2 j = (p.2 i - q.2 i) + (q.2 i - q.2 j) - (p.2 j - q.2 j) := by abel
  rw [he]
  calc
    _ ≤ ‖(p.2 i - q.2 i) + (q.2 i - q.2 j)‖ + ‖p.2 j - q.2 j‖ := norm_sub_le _ _
    _ ≤ (‖p.2 i - q.2 i‖ + ‖q.2 i - q.2 j‖) + ‖p.2 j - q.2 j‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (A + 2) * Δ := by linarith only [hi, hj, hq i j]

/-- Full numerator and actual retained polynomial on a genuine joint
complex ball. The protected neighborhood precedes N and every R. -/
theorem exists_completeNumerator_collision_ball (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ C M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ rightProductDomain S (r / 2) N,
      ∀ A Δ ρ : ℝ, 0 ≤ A → 0 < Δ → 0 < ρ → ρ ≤ Δ → ρ ≤ r / 2 →
      (∀ i j, ‖q.2 i - q.2 j‖ ≤ A * Δ) →
      ∀ p ∈ ball q ρ,
        AnalyticAt ℂ (completeRegularNumerator N) p ∧
          ‖completeRegularNumerator N p‖ ≤
            (A + 2) ^ (2 * R.card) * Δ ^ (2 * R.card) *
              (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) := by
  obtain ⟨rG, κ, C, M, hrG, hκ, hC, hM, hgauss⟩ :=
    exists_actual_retainedNumerator_analytic_gaussian S hS
  obtain ⟨rP, hrP, _, _, _, hfactor, _⟩ := exists_right_completePair_protected_neighborhood S hS
  let r := min rG rP
  have hr : 0 < r := lt_min hrG hrP
  have hrG' : r ≤ rG := min_le_left _ _
  have hrP' : r ≤ rP := min_le_right _ _
  refine ⟨r, κ, C, M, hr, hκ, hC, hM, ?_⟩
  intro N R hR q hq A Δ ρ hA hΔ _ hρΔ hρr hsep p hp
  have hpR : p ∈ rightProductDomain S r N :=
    rightProductDomain_half_ball_subset S r N q hq (ball_subset_ball hρr hp)
  have hpG := rightProductDomain_mono S hrG' N hpR
  have ha : AnalyticAt ℂ (completeRegularNumerator N) p := by
    have hh := (hgauss N ∅ (Finset.empty_subset _) p hpG).1
    rwa [retainedRegularNumerator_empty] at hh
  have hf : ∀ ij ∈ R,
      inversePairFilled explicitRightInverse (p.1, p.2 ij.1, p.2 ij.2) =
        (p.2 ij.1 - p.2 ij.2) ^ 2 *
          inversePairCollisionCoefficient explicitRightInverse (p.1, p.2 ij.1, p.2 ij.2) := by
    intro ij _
    exact hfactor _ (thickening_subset_cthickening_of_le hrP' _
      (rightPair_of_thickening hpR.1 (hpR.2 ij.1) (hpR.2 ij.2)))
  refine ⟨ha, ?_⟩
  rw [completeRegularNumerator_factorization R hR p hf, norm_mul]
  have hpoly := retainedCollisionPolynomial_norm_bound R p.2 (A + 2) Δ
    (fun ij _ => coordinate_differences_on_scaled_ball q A Δ ρ hρΔ hsep p hp ij.1 ij.2)
  exact mul_le_mul hpoly (hgauss N R hR p hpG).2 (norm_nonneg _) (by positivity)

theorem protectedJetConstant_mul_scale (k : ℕ) (c Δ : ℝ) (hΔ : Δ ≠ 0) :
    protectedJetConstant k (c * Δ) = protectedJetConstant k c / Δ ^ k := by
  have he : c * Δ = c / Δ⁻¹ := by rw [div_inv_eq_mul]
  rw [he, protectedJetConstant_div k c Δ⁻¹ (inv_ne_zero hΔ), inv_pow, div_eq_mul_inv]
  ring

/-- All fixed joint derivatives of the complete initial numerator keep
the retained collision degree, on one neighborhood before N and R.
The denominator form is valid even when the derivative exceeds D. -/
theorem exists_completeNumerator_collision_jets (S A D₀ : ℝ)
    (hS : 0 < S ∧ S < 2) (hA : 0 ≤ A) (hD₀ : 0 < D₀) :
    ∃ r κ C M c : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧ 0 < c ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ rightProductDomain S (r / 2) N,
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ D₀ → (∀ i j, ‖q.2 i - q.2 j‖ ≤ A * Δ) →
      ∀ k : ℕ,
        ‖iteratedFDeriv ℂ k (completeRegularNumerator N) q‖ ≤
          protectedJetConstant k c * (A + 2) ^ (2 * R.card) *
            (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) *
              Δ ^ (2 * R.card) / Δ ^ k := by
  obtain ⟨r, κ, C, M, hr, hκ, hC, hM, hball⟩ := exists_completeNumerator_collision_ball S hS
  let c := min 1 (r / (2 * D₀))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcr : c * D₀ ≤ r / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D₀ by positivity)).mp (min_le_right 1 (r / (2 * D₀)))
    dsimp [c]
    nlinarith only [hh]
  refine ⟨r, κ, C, M, c, hr, hκ, hC, hM, hc, ?_⟩
  intro N R hR q hq Δ hΔ hΔD hsep k
  have hρΔ : c * Δ ≤ Δ := by nlinarith only [hc1, hΔ]
  have hρr : c * Δ ≤ r / 2 := (mul_le_mul_of_nonneg_left hΔD hc.le).trans hcr
  have hall := hball N R hR q hq A Δ (c * Δ) hA hΔ (mul_pos hc hΔ) hρΔ hρr hsep
  have hj := analytic_ball_joint_jet_bound k (completeRegularNumerator N) q (c * Δ)
    ((A + 2) ^ (2 * R.card) * Δ ^ (2 * R.card) *
      (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)))
    (mul_pos hc hΔ) (fun p hp => (hall p hp).1) (fun p hp => (hall p hp).2)
  exact hj.trans_eq (by rw [protectedJetConstant_mul_scale k c Δ hΔ.ne']; ring)

end IsingBulk.AnisoF002.Isotropic
