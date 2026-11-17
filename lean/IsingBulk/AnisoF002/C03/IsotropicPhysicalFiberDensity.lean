import IsingBulk.AnisoF002.C03.IsotropicActualPositiveCoarea
import IsingBulk.AnisoF002.C03.IsotropicActualNegativeKernel
import IsingBulk.AnisoF002.C03.IsotropicKernelCurrent

/-!
# The coarea fiber density is the complete signed physical root product

Both signs are identified exactly by real phase shifts. The actual
density is continuous along the entire constraint line at positive
radial depth. These facts bind the fiber integrals to the original
physical denominators and justify ordinary interval integration.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem actualExtremeFiberDensity_continuous {N : ℕ}
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    Continuous (actualExtremeFiberDensity s η τ ξ γ θ i j) := by
  have hG : Continuous (fun t : ℝ =>
      actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t) - (γ : ℂ)) :=
    (actualTotalPhase_constrainedLine_contDiff s hs η τ ξ hη hτ hξ θ i j 0).continuous.sub continuous_const
  have hden (t : ℝ) : 1 - Complex.exp (-Complex.I *
      (actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t) - (γ : ℂ))) ≠ 0 := by
    apply complex_phase_denominator_ne_zero
    have hlocal := upperPhysicalPhase_im_neg _
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ (constrainedAngleLine θ i j t) i)
    have hsum := actualTotalPhase_attenuation_ge_individual s hs η τ ξ hη hτ hξ
      (constrainedAngleLine θ i j t) i
    change (actualPhysicalPhase η τ ξ (s, constrainedAngleLine θ i j t) i).im < 0 at hlocal
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith only [hlocal, hsum]
  exact (actualExtremeJacobian_constrainedLine_continuous s hs η τ ξ hη hτ hξ θ i j).div
    (continuous_const.sub (Complex.continuous_exp.comp (continuous_const.mul hG))).norm
    (fun t => norm_ne_zero_iff.mpr (hden t))

def actualSignedExtremeFiberDensity {N : ℕ} (s σ : ℂ) (η τ ξ : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) : ℝ :=
  ‖(1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) i) *
      (1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) j)‖ /
    ‖1 - σ * ∏ k : Fin N, isotropicInteriorRoot
      (s, actualHomotopyAngle η τ ξ (constrainedAngleLine θ i j t) k)‖

theorem phase_exp_pi_shift (z : ℂ) :
    Complex.exp (-Complex.I * (z - (Real.pi : ℂ))) = -Complex.exp (-(z * Complex.I)) := by
  rw [show -Complex.I * (z - (Real.pi : ℂ)) = -(z * Complex.I) + (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem actualExtremeFiberDensity_zero_eq_physical {N : ℕ}
    (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    actualExtremeFiberDensity s η τ ξ 0 θ i j t = actualSignedExtremeFiberDensity s 1 η τ ξ θ i j t := by
  unfold actualExtremeFiberDensity actualSignedExtremeFiberDensity
  rw [Complex.ofReal_zero, sub_zero, one_mul]
  rw [show -Complex.I * actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t) =
    -(actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t) * Complex.I) by ring,
    actualTotalPhase_exp_product]

theorem actualExtremeFiberDensity_pi_eq_physical {N : ℕ}
    (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    actualExtremeFiberDensity s η τ ξ Real.pi θ i j t =
      actualSignedExtremeFiberDensity s (-1) η τ ξ θ i j t := by
  unfold actualExtremeFiberDensity actualSignedExtremeFiberDensity
  rw [phase_exp_pi_shift, actualTotalPhase_exp_product, neg_one_mul]

/-- Exact physical sign identification, uniform along the whole fiber. -/
theorem exists_actual_signed_phase_shift {N : ℕ} (s σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (η τ ξ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) :
    ∃ γ : ℝ, ∀ t : ℝ, actualExtremeFiberDensity s η τ ξ γ θ i j t =
      actualSignedExtremeFiberDensity s σ η τ ξ θ i j t := by
  rcases hσ with rfl | rfl
  · exact ⟨0, actualExtremeFiberDensity_zero_eq_physical s η τ ξ θ i j⟩
  · exact ⟨Real.pi, actualExtremeFiberDensity_pi_eq_physical s η τ ξ θ i j⟩

theorem exists_actual_positive_signed_extreme_integral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ positiveExtremeFiber θ i j b δ r →
        ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ t in A..B, actualSignedExtremeFiberDensity (isotropicRadialParameter α ε) σ η τ ξ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ :=
    exists_actual_positive_extreme_integral α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r A B hr hAB hfiber σ hσ
  obtain ⟨γ, hγ⟩ := exists_actual_signed_phase_shift (isotropicRadialParameter α ε) σ hσ η τ ξ θ i j
  have he := funext hγ
  rw [← he]
  exact hbound N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber

end IsingBulk.AnisoF002.Isotropic
