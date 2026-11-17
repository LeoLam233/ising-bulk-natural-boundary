import IsingBulk.AnisoF002.C03.IsotropicInitialCollisionJets
import IsingBulk.AnisoF002.C03.IsotropicActualSharpCovarianceJets

/-!
# Retained-degree initial jets on every actual right shell

All protected-domain and shell-scale assumptions are now discharged
for the actual full balanced image. The resulting bound is the
complete initial regular numerator estimate used by the exact current
recurrence, with all parameter and coordinate derivatives included.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_actual_completeNumerator_collision_jets (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) → (∃ i j, r ≤ |θ i - θ j|) →
        let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
        let Δ := isotropicShellDelta b ε r θ
        ‖iteratedFDeriv ℂ k (completeRegularNumerator N) q‖ ≤
          Ck * C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) *
            Δ ^ (2 * R.card) / Δ ^ k := by
  obtain ⟨δA, A, hδA, _, hA, hcoord⟩ :=
    exists_actual_whole_arc_shell_coordinate_scale α b η hα hb hpoint hη hwidth
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
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨R₀, κ, C, M, c, hR₀, hκ, hC, hM, hc, hjets⟩ :=
    exists_completeNumerator_collision_jets (2 * Real.cos α) A D₀ hS hA.le hD₀
  obtain ⟨δD, hδD, hdomain⟩ := exists_actual_right_homotopy_domain
    (2 * Real.cos α) (R₀ / 2) hS (half_pos hR₀)
  let δ := min 1 (min δA (δD / 8))
  let M₁ := (A + 2) ^ 2 * M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδA' : δ ≤ δA := (min_le_right _ _).trans (min_le_left _ _)
  have hδD8 : δ ≤ δD / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hδD' : δ ≤ δD := by linarith only [hδD8, hδD]
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨δ, κ, C, M₁, hδ, hδ1, hκ, hC, hM₁, ?_⟩
  intro k
  refine ⟨protectedJetConstant k c, protectedJetConstant_pos k hc, ?_⟩
  intro N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) < δD :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδD8, hδD])
  have hθD : ∀ i, θ i ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - δD) δD := by
    intro i
    rw [hbS]
    exact ⟨by linarith only [(hθ i).1, hδD'], (hθ i).2.trans hδD'⟩
  have hq : q ∈ rightProductDomain (2 * Real.cos α) (R₀ / 2) N :=
    (hdomain N hN _ hrad.2.2.2.1 hsnear η τ ξ hη
      ⟨hτ.1, hτ.2.trans hδD'⟩ hξ θ hθD).1
  have hcoord' (i j : Fin N) : ‖q.2 i - q.2 j‖ ≤ A * Δ := by
    have hh := hcoord N hN ε hε (hεδ.trans hδA') τ ξ ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
      (fun l => ⟨by linarith only [(hθ l).1, hb.2, hδA'], (hθ l).2.trans hδA'⟩) r hr hdiam i j
    exact hh.trans_eq (by dsimp [Δ, isotropicShellDelta, isotropicShellT]; ring)
  have hrmax : r ≤ Real.pi + 2 := by
    obtain ⟨i, j, hij⟩ := hdiamLower
    have hg : |θ i - θ j| ≤ b + 2 * δ :=
      abs_le.mpr ⟨by linarith only [(hθ i).1, (hθ j).2],
        by linarith only [(hθ i).2, (hθ j).1]⟩
    linarith only [hij, hg, hb.2, hδ1]
  have hT : 0 < isotropicShellT b ε r θ := by unfold isotropicShellT; positivity
  have hrT : r ≤ isotropicShellT b ε r θ := by
    unfold isotropicShellT
    linarith only [abs_nonneg (angularMean (fun l => θ l + b)), hε]
  have hΔroot : Δ ≤ Real.sqrt r := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hT)).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrT) (Real.sqrt_nonneg r)
    simpa only [Real.mul_self_sqrt hr.le] using hh
  have hΔD : Δ ≤ D₀ := hΔroot.trans (Real.sqrt_le_sqrt hrmax)
  have hh := hjets N R hR q hq Δ hΔ hΔD hcoord' k
  have hpow : M₁ ^ R.card = (A + 2) ^ (2 * R.card) * M ^ R.card := by
    dsimp only [M₁]
    rw [mul_pow, ← pow_mul]
  exact hh.trans_eq (by rw [hpow]; ring)

end IsingBulk.AnisoF002.Isotropic
