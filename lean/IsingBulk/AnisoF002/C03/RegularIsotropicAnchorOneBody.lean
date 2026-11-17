import IsingBulk.AnisoF002.C03.RegularIsotropicPositivePeriod
import IsingBulk.AnisoF002.C03.RegularIsotropicActualAnchorDisks

/-!
# Genuine one-body L1 control on the compact one-sided anchor interval

Two continuous translated physical envelopes cover the endpoint sliver
without selecting a discontinuous representative. The integral bound is
uniform in epsilon, both occupancy fractions and all particle numbers.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

def anchorOneBodyMajorant (b C ε θ : ℝ) : ℝ :=
  fullCircleOneBodyMajorant b C ε θ + fullCircleOneBodyMajorant b C ε (θ + 2 * Real.pi)

theorem anchorOneBodyMajorant_continuous (b C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (anchorOneBodyMajorant b C ε) :=
  (fullCircleOneBodyMajorant_continuous b C hε).add
    ((fullCircleOneBodyMajorant_continuous b C hε).comp (continuous_id.add continuous_const))

theorem anchorOneBodyMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (b ε θ : ℝ) :
    0 ≤ anchorOneBodyMajorant b C ε θ :=
  add_nonneg (fullCircleOneBodyMajorant_nonneg hC b ε θ)
    (fullCircleOneBodyMajorant_nonneg hC b ε (θ + 2 * Real.pi))

theorem fullCircleOneBodyMajorant_arbitrary_period (b C ε a d : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    (∫ θ in a..(a + 2 * Real.pi), fullCircleOneBodyMajorant b C ε (θ + d)) ≤
      26 * Real.pi * C := by
  have hh := fullCircleOneBodyMajorant_positive_shift_integral b C ε (a + d) hC hε
  rw [intervalIntegral.integral_comp_add_right] at hh ⊢
  simpa only [zero_add, show 2 * Real.pi + (a + d) = a + 2 * Real.pi + d by ring] using hh

theorem anchorOneBodyMajorant_integral_bound (b C ε ρ : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (_hρ : 0 ≤ ρ) (hρπ : ρ ≤ Real.pi / 2) :
    (∫ θ in Icc (-Real.pi - ρ) ρ, anchorOneBodyMajorant b C ε θ) ≤
      52 * Real.pi * C := by
  have hcont := anchorOneBodyMajorant_continuous b C hε
  have hi : IntegrableOn (anchorOneBodyMajorant b C ε) (Icc (-Real.pi - ρ) (Real.pi - ρ)) volume :=
    hcont.continuousOn.integrableOn_Icc
  have hsub : Icc (-Real.pi - ρ) ρ ⊆ Icc (-Real.pi - ρ) (Real.pi - ρ) :=
    fun _ hx => ⟨hx.1, hx.2.trans (by linarith only [hρπ])⟩
  have hmono := setIntegral_mono_set hi (Eventually.of_forall (anchorOneBodyMajorant_nonneg hC b ε))
    (Eventually.of_forall hsub)
  apply hmono.trans
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [Real.pi_pos])]
  have hA : IntervalIntegrable (fullCircleOneBodyMajorant b C ε) volume (-Real.pi - ρ) (Real.pi - ρ) :=
    (fullCircleOneBodyMajorant_continuous b C hε).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun θ => fullCircleOneBodyMajorant b C ε (θ + 2 * Real.pi))
      volume (-Real.pi - ρ) (Real.pi - ρ) :=
    ((fullCircleOneBodyMajorant_continuous b C hε).comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  change (∫ θ in (-Real.pi - ρ)..(Real.pi - ρ),
    fullCircleOneBodyMajorant b C ε θ + fullCircleOneBodyMajorant b C ε (θ + 2 * Real.pi)) ≤ _
  rw [intervalIntegral.integral_add hA hB]
  have ha := fullCircleOneBodyMajorant_arbitrary_period b C ε (-Real.pi - ρ) 0 hC hε
  have hb := fullCircleOneBodyMajorant_arbitrary_period b C ε (-Real.pi - ρ) (2 * Real.pi) hC hε
  rw [show -Real.pi - ρ + 2 * Real.pi = Real.pi - ρ by ring] at ha hb
  simp only [add_zero] at ha
  linarith only [ha, hb]

theorem exists_anchor_oneBody_L1_majorant (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.pi / 2 →
        Continuous (anchorOneBodyMajorant b C ε) ∧
        (∀ θ, 0 ≤ anchorOneBodyMajorant b C ε θ) ∧
        IntegrableOn (anchorOneBodyMajorant b C ε) (Icc (-Real.pi - ρ) ρ) volume ∧
        (∫ θ in Icc (-Real.pi - ρ) ρ, anchorOneBodyMajorant b C ε θ) ≤ 52 * Real.pi * C ∧
        ∀ τ P Q : ℝ, τ ∈ Icc 0 δ → P ∈ Icc 0 1 → Q ∈ Icc 0 1 →
        ∀ θ ∈ Icc (-Real.pi - ρ) ρ,
          ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ P Q θ) /
            (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ P Q θ) ^ 2)‖ ≤
            anchorOneBodyMajorant b C ε θ := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ := exists_full_circle_oneBody_pointwise α b hα hb hpoint
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro η hη hwidth ε hε hεδ ρ hρ hρπ
  have hcont := anchorOneBodyMajorant_continuous b C hε
  refine ⟨hcont, anchorOneBodyMajorant_nonneg hC.le b ε, hcont.continuousOn.integrableOn_Icc,
    anchorOneBodyMajorant_integral_bound b C ε ρ hC.le hε hρ hρπ, ?_⟩
  intro τ P Q hτ hP hQ θ hθ
  by_cases hlo : -Real.pi ≤ θ
  · exact (hbound η hη hwidth ε hε hεδ τ P Q hτ hP hQ θ
      ⟨hlo, hθ.2.trans (by linarith only [hρπ, Real.pi_pos])⟩).trans
      (le_add_of_nonneg_right (fullCircleOneBodyMajorant_nonneg hC.le b ε _))
  · have hh := hbound η hη hwidth ε hε hεδ τ P Q hτ hP hQ (θ + 2 * Real.pi)
      ⟨by linarith only [hθ.1, hρπ, Real.pi_pos], by linarith⟩
    rw [fixedOccupancyAngle_add_two_pi] at hh
    simp only [isotropicInteriorRoot, isotropicDispersion, Complex.cos_add_two_pi] at hh
    exact hh.trans (le_add_of_nonneg_left (fullCircleOneBodyMajorant_nonneg hC.le b ε θ))

theorem actualCoordinateMultiplier_norm_bound {N : ℕ} (hN : 0 < N)
    (S : ℂ) (η τ : ℝ) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) (i : Fin N) :
    ‖actualCoordinateMultiplier η τ 1 (S, θ) i‖ ≤
      1 + Real.exp 1 * ‖2 * isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) /
        (1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ := by
  change ‖1 - Complex.sin (actualHomotopyAngle η τ 1 θ i) /
    Complex.sin (actualPhysicalPhase η τ 1 (S, θ) i)‖ ≤ _
  have hh := norm_sub_le (1 : ℂ) (Complex.sin (actualHomotopyAngle η τ 1 θ i) /
    Complex.sin (actualPhysicalPhase η τ 1 (S, θ) i))
  rw [norm_one, norm_div, div_eq_mul_inv] at hh
  rw [isotropic_oneBody_norm]
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (actual_balanced_sin_norm_bound hN η τ hτ θ i) (inv_nonneg.mpr (norm_nonneg _))))

end IsingBulk.AnisoF002.Isotropic
