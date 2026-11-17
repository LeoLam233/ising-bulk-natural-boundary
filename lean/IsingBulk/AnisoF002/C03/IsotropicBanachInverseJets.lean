import IsingBulk.AnisoF002.C03.IsotropicUniformJets
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Dimension-independent jets of inversion near the identity

The full balanced Jacobian is an operator close to the identity. This
generic Banach-algebra estimate controls all inverse jets by a single
complex ball; restricting scalars gives the real jets needed for smooth
angular cutoffs. No analyticity of the cutoff is used.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [NormedAlgebra ℂ A] in
theorem banach_inverse_near_one_bound (z : A) (hz : ‖z - 1‖ ≤ (3 / 4 : ℝ)) :
    IsUnit z ∧ ‖Ring.inverse z‖ ≤ 4 := by
  have hn : ‖1 - z‖ < 1 := by rw [norm_sub_rev]; linarith only [hz]
  have hu : IsUnit z := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  refine ⟨hu, ?_⟩
  have he : Ring.inverse z = 1 + Ring.inverse z * (1 - z) := by
    rw [mul_sub, mul_one, Ring.inverse_mul_cancel z hu]
    abel
  have hnorm : ‖Ring.inverse z‖ ≤ 1 + ‖Ring.inverse z‖ * (3 / 4 : ℝ) := by
    calc
      _ = ‖1 + Ring.inverse z * (1 - z)‖ := congrArg norm he
      _ ≤ ‖(1 : A)‖ + ‖Ring.inverse z * (1 - z)‖ := norm_add_le _ _
      _ ≤ 1 + ‖Ring.inverse z‖ * ‖1 - z‖ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_mul_le _ _)
      _ ≤ _ := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hz) (norm_nonneg _)
  linarith only [hnorm]

theorem banach_inverse_protected_ball (a : A) (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ)) :
    ∀ z ∈ ball a (1 / 4 : ℝ), AnalyticAt ℂ Ring.inverse z ∧ ‖Ring.inverse z‖ ≤ 4 := by
  intro z hz
  have hz' : ‖z - 1‖ ≤ (3 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm] at hz
    have htri : ‖z - 1‖ ≤ ‖z - a‖ + ‖a - 1‖ := by
      simpa only [dist_eq_norm] using dist_triangle z a 1
    linarith only [htri, hz, ha]
  obtain ⟨hu, hbound⟩ := banach_inverse_near_one_bound z hz'
  exact ⟨analyticOnNhd_inverse z hu, hbound⟩

theorem banach_inverse_complex_jet_bound (a : A) (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ)) (k : ℕ) :
    ‖iteratedFDeriv ℂ k Ring.inverse a‖ ≤ 4 * protectedJetConstant k (1 / 4 : ℝ) := by
  have hh := banach_inverse_protected_ball a ha
  exact (analytic_ball_joint_jet_bound k Ring.inverse a (1 / 4) 4 (by norm_num)
    (fun z hz => (hh z hz).1) (fun z hz => (hh z hz).2)).trans_eq (mul_comm _ _)

theorem analytic_real_iteratedFDeriv_norm_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (x : E) (hf : AnalyticAt ℂ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f x‖ = ‖iteratedFDeriv ℂ k f x‖ := by
  have hh := (hf.contDiffAt (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  rw [← hh]
  exact ContinuousMultilinearMap.norm_restrictScalars _

theorem banach_inverse_real_jet_bound (a : A) (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k Ring.inverse a‖ ≤ 4 * protectedJetConstant k (1 / 4 : ℝ) := by
  have hh := (banach_inverse_protected_ball a ha) a (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 4))
  rw [analytic_real_iteratedFDeriv_norm_eq Ring.inverse a hh.1 k]
  exact banach_inverse_complex_jet_bound a ha k

end IsingBulk.AnisoF002.Isotropic
