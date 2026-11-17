import IsingBulk.AnisoF002.C03.IsotropicDeformationSheet
import IsingBulk.AnisoF002.Isotropic.RightArc
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Explicit smooth periodic bumps and the actual balanced homotopy

The upper bump is constructed, not assumed. It vanishes on fixed endpoint
slivers, equals one near the selected branch, and its reflection is the
lower bump. The resulting actual homotopy preserves the constraint and
the interior spectral sheet, with displacement bounded uniformly in N.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

def upperPeriodicBump (η θ : ℝ) : ℝ :=
  Real.smoothTransition ((Real.sin θ - η) / η)

def lowerPeriodicBump (η θ : ℝ) : ℝ := upperPeriodicBump η (-θ)

theorem upperPeriodicBump_bounds (η θ : ℝ) :
    0 ≤ upperPeriodicBump η θ ∧ upperPeriodicBump η θ ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem lowerPeriodicBump_bounds (η θ : ℝ) :
    0 ≤ lowerPeriodicBump η θ ∧ lowerPeriodicBump η θ ≤ 1 :=
  upperPeriodicBump_bounds η (-θ)

theorem upperPeriodicBump_contDiff (η : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (upperPeriodicBump η) :=
  Real.smoothTransition.contDiff.comp ((Real.contDiff_sin.sub contDiff_const).div_const η)

theorem lowerPeriodicBump_contDiff (η : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (lowerPeriodicBump η) :=
  (upperPeriodicBump_contDiff η).comp contDiff_neg

theorem upperPeriodicBump_periodic (η : ℝ) :
    Function.Periodic (upperPeriodicBump η) (2 * Real.pi) := by
  intro θ
  simp [upperPeriodicBump, Real.sin_add_two_pi]

theorem lowerPeriodicBump_periodic (η : ℝ) :
    Function.Periodic (lowerPeriodicBump η) (2 * Real.pi) := by
  intro θ
  unfold lowerPeriodicBump upperPeriodicBump
  rw [show -(θ + 2 * Real.pi) = -θ - 2 * Real.pi by ring, Real.sin_sub_two_pi]

theorem upperPeriodicBump_zero {η θ : ℝ} (hη : 0 < η) (hθ : Real.sin θ ≤ η) :
    upperPeriodicBump η θ = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) hη.le)

theorem upperPeriodicBump_one {η θ : ℝ} (hη : 0 < η) (hθ : 2 * η ≤ Real.sin θ) :
    upperPeriodicBump η θ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div hη).mpr
  linarith

theorem actual_bump_sine_signs {η : ℝ} (hη : 0 < η) (θ : ℝ) :
    0 ≤ upperPeriodicBump η θ * Real.sin θ ∧
      lowerPeriodicBump η θ * Real.sin θ ≤ 0 := by
  constructor
  · by_cases hθ : 0 ≤ Real.sin θ
    · exact mul_nonneg (upperPeriodicBump_bounds η θ).1 hθ
    · rw [upperPeriodicBump_zero hη (le_trans (le_of_not_ge hθ) hη.le), zero_mul]
  · by_cases hθ : Real.sin θ ≤ 0
    · exact mul_nonpos_of_nonneg_of_nonpos (lowerPeriodicBump_bounds η θ).1 hθ
    · have hz : lowerPeriodicBump η θ = 0 := by
        apply upperPeriodicBump_zero hη
        rw [Real.sin_neg]
        linarith
      rw [hz, zero_mul]

theorem actual_bump_endpoint_slivers {η θ : ℝ} (hη : 0 < η)
    (hθ : |Real.sin θ| ≤ η) :
    upperPeriodicBump η θ = 0 ∧ lowerPeriodicBump η θ = 0 := by
  refine ⟨upperPeriodicBump_zero hη (abs_le.mp hθ).2, ?_⟩
  apply upperPeriodicBump_zero hη
  rw [Real.sin_neg]
  linarith [(abs_le.mp hθ).1]

def branchBumpWidth (S : ℝ) : ℝ := Real.sin (rightBranchEndpoint S) / 4

theorem branchBumpWidth_pos (S : ℝ) (hS : 0 < S ∧ S < 2) :
    0 < branchBumpWidth S :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi (rightBranchEndpoint_pos S hS.2)
    (rightBranchEndpoint_lt_pi S hS.1)) (by norm_num)

theorem actual_bumps_branch_plateau (S : ℝ) (hS : 0 < S ∧ S < 2) :
    upperPeriodicBump (branchBumpWidth S) (rightBranchEndpoint S) = 1 ∧
      lowerPeriodicBump (branchBumpWidth S) (-rightBranchEndpoint S) = 1 ∧
      upperPeriodicBump (branchBumpWidth S) (-rightBranchEndpoint S) = 0 ∧
      lowerPeriodicBump (branchBumpWidth S) (rightBranchEndpoint S) = 0 := by
  have hη := branchBumpWidth_pos S hS
  have hsin : 0 < Real.sin (rightBranchEndpoint S) := by
    have h := hη
    dsimp [branchBumpWidth] at h
    linarith
  have hp : upperPeriodicBump (branchBumpWidth S) (rightBranchEndpoint S) = 1 := by
    apply upperPeriodicBump_one hη
    dsimp [branchBumpWidth]
    linarith
  have hm : upperPeriodicBump (branchBumpWidth S) (-rightBranchEndpoint S) = 0 := by
    apply upperPeriodicBump_zero hη
    rw [Real.sin_neg]
    linarith
  exact ⟨hp, by simpa only [lowerPeriodicBump, neg_neg] using hp, hm, hm⟩

variable {ι : Type*} [Fintype ι]

/-- The full population dependence cancels N in the pointwise shift,
uniformly over all actual occupancy fractions in [0,1]. -/
theorem balancedShift_abs_le (τ : ℝ) (hτ : 0 ≤ τ) (p m : ι → ℝ)
    (hN : 0 < Fintype.card ι)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1) (i : ι) :
    |balancedShift (τ / Fintype.card ι) p m i| ≤ τ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hP := bump_population_bounds p hp
  have hQ := bump_population_bounds m hm
  have h₁ : 0 ≤ (∑ j, p j) * m i := mul_nonneg hP.1 (hm i).1
  have h₂ : 0 ≤ (∑ j, m j) * p i := mul_nonneg hQ.1 (hp i).1
  have h₃ : (∑ j, p j) * m i ≤ Fintype.card ι := by
    exact (mul_le_mul hP.2 (hm i).2 (hm i).1 hn.le).trans_eq (mul_one _)
  have h₄ : (∑ j, m j) * p i ≤ Fintype.card ι := by
    exact (mul_le_mul hQ.2 (hp i).2 (hp i).1 hn.le).trans_eq (mul_one _)
  have hdiff : |(∑ j, p j) * m i - (∑ j, m j) * p i| ≤ Fintype.card ι := by
    rw [abs_le]
    constructor <;> linarith
  rw [balancedShift, abs_mul, abs_of_nonneg (div_nonneg hτ hn.le)]
  exact (mul_le_mul_of_nonneg_left hdiff (div_nonneg hτ hn.le)).trans_eq
    (div_mul_cancel₀ τ hn.ne')

/-- The explicit smooth bumps discharge every sign condition in the
sheet theorem for the whole constrained torus and every homotopy time. -/
theorem actual_balanced_homotopy_sheet (S : ℂ) (hS : 0 < S.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (θ : ι → ℝ) :
    ∀ i, 0 < (isotropicDispersion (S,
      balancedHomotopyCoordinate τ θ (fun j => upperPeriodicBump η (θ j))
        (fun j => lowerPeriodicBump η (θ j)) ξ i)).im := by
  apply balancedHomotopy_dispersion_im_pos S hS τ ξ hτ hξ θ
  · intro i
    exact (upperPeriodicBump_bounds η (θ i)).1
  · intro i
    exact (lowerPeriodicBump_bounds η (θ i)).1
  · intro i
    exact (actual_bump_sine_signs hη (θ i)).1
  · intro i
    exact (actual_bump_sine_signs hη (θ i)).2

theorem actual_balanced_homotopy_displacement (η τ ξ : ℝ) (hτ : 0 ≤ τ)
    (hξ : ξ ∈ Icc 0 1) (θ : ι → ℝ) (hN : 0 < Fintype.card ι) (i : ι) :
    ‖balancedHomotopyCoordinate τ θ (fun j => upperPeriodicBump η (θ j))
        (fun j => lowerPeriodicBump η (θ j)) ξ i - (θ i : ℂ)‖ ≤ τ := by
  have hshift := balancedShift_abs_le (ξ * τ) (mul_nonneg hξ.1 hτ)
    (fun j => upperPeriodicBump η (θ j)) (fun j => lowerPeriodicBump η (θ j)) hN
    (fun j => upperPeriodicBump_bounds η (θ j)) (fun j => lowerPeriodicBump_bounds η (θ j)) i
  have he : ξ * (τ / (Fintype.card ι : ℝ)) = (ξ * τ) / Fintype.card ι := by ring
  simp only [balancedHomotopyCoordinate, contourCoordinate, he, sub_sub_cancel_left,
    norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact hshift.trans (by nlinarith [hξ.2])

end IsingBulk.AnisoF002.Isotropic
