import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorOneBody
import IsingBulk.AnisoF002.C03.IsotropicActualDeterminantBound

/-!
# The full actual anchored Jacobian has an independent-coordinate L1 envelope

The named factor has a genuine compact exterior root gap. Every other
factor is the original inverse-sine one-body factor and has its uniform
integrable angular majorant. The full balanced determinant is retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory

def anchorJacobianWeight (b C ε θ : ℝ) : ℝ :=
  1 + Real.exp 1 * anchorOneBodyMajorant b C ε θ

theorem anchorJacobianWeight_continuous (b C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (anchorJacobianWeight b C ε) :=
  continuous_const.add (continuous_const.mul (anchorOneBodyMajorant_continuous b C hε))

theorem anchorJacobianWeight_nonneg {C : ℝ} (hC : 0 ≤ C) (b ε θ : ℝ) :
    0 ≤ anchorJacobianWeight b C ε θ :=
  add_nonneg zero_le_one (mul_nonneg (Real.exp_nonneg _) (anchorOneBodyMajorant_nonneg hC b ε θ))

theorem anchorJacobianWeight_integral_bound (b C ε ρ : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρπ : ρ ≤ Real.pi / 2) :
    (∫ θ in Icc (-Real.pi - ρ) ρ, anchorJacobianWeight b C ε θ) ≤
      2 * Real.pi + Real.exp 1 * (52 * Real.pi * C) := by
  have hbody := anchorOneBodyMajorant_integral_bound b C ε ρ hC hε hρ hρπ
  have hle : -Real.pi - ρ ≤ ρ := by linarith only [Real.pi_pos, hρ]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle] at hbody ⊢
  have hi : IntervalIntegrable (anchorOneBodyMajorant b C ε) volume (-Real.pi - ρ) ρ :=
    (anchorOneBodyMajorant_continuous b C hε).intervalIntegrable _ _
  change (∫ θ in (-Real.pi - ρ)..ρ, 1 + Real.exp 1 * anchorOneBodyMajorant b C ε θ) ≤ _
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul, mul_one]
  exact add_le_add (by linarith only [hρπ]) (mul_le_mul_of_nonneg_left hbody (Real.exp_nonneg _))

theorem exists_actual_anchored_jacobian_majorant (α b c : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hc : 0 < c) :
    ∃ C H A : ℝ, 0 < C ∧ 0 < H ∧ 0 < A ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.pi / 2 →
        Continuous (anchorJacobianWeight b C ε) ∧
        (∀ θ, 0 ≤ anchorJacobianWeight b C ε θ) ∧
        IntegrableOn (anchorJacobianWeight b C ε) (Icc (-Real.pi - ρ) ρ) volume ∧
        (∫ θ in Icc (-Real.pi - ρ) ρ, anchorJacobianWeight b C ε θ) ≤ H ∧
        ∀ N : ℕ, 0 < N → ∀ a : Fin N, ∀ τ ∈ Icc 0 δ, ∀ θ : Fin N → ℝ,
        (∀ i, θ i ∈ Icc (-Real.pi - ρ) ρ) → c ≤ Real.cos b - Real.cos (θ a) →
          ‖actualCoordinateDeterminant η τ 1 (isotropicRadialParameter α ε, θ)‖ ≤
            (2 : ℝ) ^ N * A *
              ∏ i ∈ Finset.univ.erase a, anchorJacobianWeight b C ε (θ i) := by
  obtain ⟨δB, C, hδB, hδB1, hC, hbody⟩ := exists_anchor_oneBody_L1_majorant α b hα hb hpoint
  let q₀ := exteriorAnchorRootBound c
  have hq₀ : 0 < q₀ ∧ q₀ < 1 := exteriorAnchorRootBound_spec hc
  let A := 1 + Real.exp 1 * (2 / (1 - q₀ ^ 2))
  have hqgap : 0 < 1 - q₀ ^ 2 := by nlinarith [hq₀.1, hq₀.2]
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C, 2 * Real.pi + Real.exp 1 * (52 * Real.pi * C), A, hC, by positivity, hA, ?_⟩
  intro η hη hwidth
  obtain ⟨δM, hδM, _, hdet⟩ := exists_actual_balanced_determinant_bound η
  let δ := min δB (min δM (c / 12))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdB : δ ≤ δB := min_le_left _ _
  have hdM : δ ≤ δM := (min_le_right _ _).trans (min_le_left _ _)
  have hdc : δ ≤ c / 12 := (min_le_right _ _).trans (min_le_right _ _)
  have hd1 : δ ≤ 1 := hdB.trans hδB1
  refine ⟨δ, hδ, hd1, ?_⟩
  intro ε hε hεδ ρ hρ hρπ
  have hcont := anchorJacobianWeight_continuous b C hε
  refine ⟨hcont, anchorJacobianWeight_nonneg hC.le b ε, hcont.continuousOn.integrableOn_Icc,
    anchorJacobianWeight_integral_bound b C ε ρ hC.le hε hρ hρπ, ?_⟩
  intro N hN a τ hτ θ hθ hcos
  have hτ1 : τ ∈ Icc 0 1 := ⟨hτ.1, hτ.2.trans hd1⟩
  have hε1 : ε ≤ 1 := hεδ.trans hd1
  have hsmall : 4 * ε + 2 * τ ≤ c / 2 := by linarith only [hεδ, hτ.2, hdc]
  have hroot := actual_exterior_anchor_root_bound hN α b ε η τ c hα hpoint hε hε1 hη hτ1 hc hsmall θ a hcos
  have ha : ‖actualCoordinateMultiplier η τ 1 (isotropicRadialParameter α ε, θ) a‖ ≤ A :=
    (actualCoordinateMultiplier_norm_bound hN _ η τ hτ1 θ a).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (root_oneBody_bound_of_norm_gap hq₀.1.le hq₀.2 hroot) (Real.exp_nonneg _)))
  have hm (i : Fin N) : ‖actualCoordinateMultiplier η τ 1 (isotropicRadialParameter α ε, θ) i‖ ≤
      anchorJacobianWeight b C ε (θ i) := by
    have hi := (hbody η hη hwidth ε hε (hεδ.trans hdB) ρ hρ hρπ).2.2.2.2 τ
      (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) ⟨hτ.1, hτ.2.trans hdB⟩
      (actualUpperOccupancy_mem_Icc hN η θ) (actualLowerOccupancy_mem_Icc hN η θ) (θ i) (hθ i)
    rw [← one_mul τ, ← actualHomotopyAngle_eq_fixedOccupancy η τ 1 θ i] at hi
    exact (actualCoordinateMultiplier_norm_bound hN _ η τ hτ1 θ i).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)))
  have hrad := isotropicRadialParameter_estimates α ε hα hε hε1
  have hprod : (∏ i : Fin N, ‖actualCoordinateMultiplier η τ 1 (isotropicRadialParameter α ε, θ) i‖) ≤
      A * ∏ i ∈ Finset.univ.erase a, anchorJacobianWeight b C ε (θ i) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
      (fun i => ‖actualCoordinateMultiplier η τ 1 (isotropicRadialParameter α ε, θ) i‖)
      (Finset.mem_univ a)]
    exact mul_le_mul ha (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hm i))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hA.le
  rw [actualCoordinateDeterminant_factorization η τ 1 _
    (fun i => actual_balanced_homotopy_sheet _ hrad.2.2.2.1 η τ 1 hη hτ.1 zero_le_one θ i),
    norm_mul, norm_prod]
  exact (mul_le_mul (hdet N hN τ 1 ⟨hτ.1, hτ.2.trans hdM⟩ (by norm_num) θ) hprod
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)).trans_eq (by ring)

end IsingBulk.AnisoF002.Isotropic
