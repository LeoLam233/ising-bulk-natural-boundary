import IsingBulk.AnisoF002.C03.IsotropicFullDensityFiber
import IsingBulk.AnisoF002.C03.NegativeGaussianSymmetry

/-!
# Exact Lebesgue changes between constrained angular charts

This reuses only the independent F002 generic constrained-plane chart
and its permutation measure preservation. Translation to an arbitrary
angular mean preserves the original graph-coordinate normalization.
The full balanced physical density is invariant under the actual
particle permutation, including both full bump populations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory
open IsingBulk.AnisoF002.NegativeHT.Angular

def constrainedChartPermutation {d : ℕ} (σ : Equiv.Perm (Fin (d + 1))) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  (independentChart d).trans ((constrainedPerm σ).toLinearEquiv.trans (independentChart d).symm)

theorem constrainedChartPermutation_measurePreserving {d : ℕ} (σ : Equiv.Perm (Fin (d + 1))) :
    MeasurePreserving (constrainedChartPermutation σ) volume volume := by
  let e := (independentChart d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hinv : MeasurePreserving e.symm (independentMeasure d) volume :=
    MeasurePreserving.symm e (independentChart_measurePreserving d)
  exact hinv.comp ((constrainedPerm_independent_measurePreserving σ).comp
    (independentChart_measurePreserving d))

theorem constrainedChartPermutation_integral {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin d → ℝ) → E) :
    (∫ x, f (constrainedChartPermutation σ x)) = ∫ x, f x :=
  (constrainedChartPermutation_measurePreserving σ).integral_comp'
    (f := (constrainedChartPermutation σ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv) f

def centeredConstraintAngles {d : ℕ} (a : ℝ) (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun i => a + (independentChart d x : Ambient d) i

theorem centeredConstraintAngles_sum {d : ℕ} (a : ℝ) (x : Fin d → ℝ) :
    ∑ i, centeredConstraintAngles a x i = (d + 1 : ℝ) * a := by
  simp only [centeredConstraintAngles]
  rw [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, constrained_sum, add_zero]
  push_cast
  rfl

theorem centeredConstraintAngles_eq_snoc {d : ℕ} (a : ℝ) (x : Fin d → ℝ) :
    centeredConstraintAngles a x =
      Fin.snoc (fun i => a + x i) ((d + 1 : ℝ) * a - ∑ i, (a + x i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [centeredConstraintAngles, independentChart_last, Fin.snoc_last,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · simp only [centeredConstraintAngles, independentChart_castSucc, Fin.snoc_castSucc]

theorem centeredConstraintAngles_chartPermutation {d : ℕ}
    (σ : Equiv.Perm (Fin (d + 1))) (a : ℝ) (x : Fin d → ℝ) :
    centeredConstraintAngles a (constrainedChartPermutation σ x) =
      fun i => centeredConstraintAngles a x (σ i) := by
  funext i
  change a + (independentChart d ((independentChart d).symm
    (constrainedPerm σ (independentChart d x))) : Ambient d) i = _
  rw [LinearEquiv.apply_symm_apply, constrainedPerm_apply]
  rfl

theorem actualHomotopyAngle_perm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (η τ ξ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    actualHomotopyAngle η τ ξ (fun k => θ (σ k)) i = actualHomotopyAngle η τ ξ θ (σ i) := by
  have hp := Equiv.sum_comp σ (fun k => upperPeriodicBump η (θ k))
  have hm := Equiv.sum_comp σ (fun k => lowerPeriodicBump η (θ k))
  simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
    balancedShift, hp, hm]

theorem actualPhaseSlope_perm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    actualPhaseSlope s η τ ξ (fun k => θ (σ k)) i = actualPhaseSlope s η τ ξ θ (σ i) := by
  rw [actualPhaseSlope, actualHomotopyAngle_perm]
  rfl

theorem actualTotalPhase_perm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    actualTotalPhase η τ ξ (s, fun k => θ (σ k)) = actualTotalPhase η τ ξ (s, θ) := by
  simp only [actualTotalPhase, actualPhysicalPhase]
  simp_rw [actualHomotopyAngle_perm]
  exact Equiv.sum_comp σ (fun k =>
    upperPhysicalPhase (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ k)))

theorem actualFullPhaseDensity_perm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (s : ℂ) (η τ ξ γ : ℝ) (θ : Fin N → ℝ) :
    actualFullPhaseDensity s η τ ξ γ (fun k => θ (σ k)) = actualFullPhaseDensity s η τ ξ γ θ := by
  unfold actualFullPhaseDensity
  rw [actualTotalPhase_perm]
  congr 1
  simp_rw [actualPhaseSlope_perm]
  exact Equiv.prod_comp σ (fun k => ‖1 + actualPhaseSlope s η τ ξ θ k‖)

theorem actualFullPhaseDensity_centered_chart_invariant {d : ℕ}
    (σ : Equiv.Perm (Fin (d + 1))) (s : ℂ) (η τ ξ γ a : ℝ) (x : Fin d → ℝ) :
    actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles a (constrainedChartPermutation σ x)) =
      actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles a x) := by
  rw [centeredConstraintAngles_chartPermutation, actualFullPhaseDensity_perm]

end IsingBulk.AnisoF002.Isotropic
