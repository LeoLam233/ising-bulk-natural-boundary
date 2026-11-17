import IsingBulk.AnisoF002.C03.IsotropicWholeArcShellScales

/-!
# The actual population alternatives in the inverse-coordinate scale

Zero upper population removes every actual displacement. A positive
upper population forces a positive angle and therefore a uniform lower
bound for T. Both alternatives concern the original complete tuple.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem upperBumps_zero_of_actualUpperOccupancy_zero {N : ℕ} (hN : 0 < N)
    (η : ℝ) (θ : Fin N → ℝ) (hP : actualUpperOccupancy η θ = 0) :
    ∀ i, upperPeriodicBump η (θ i) = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hsum : (∑ i, upperPeriodicBump η (θ i)) = 0 :=
    (div_eq_zero_iff.mp hP).resolve_right hn
  intro i
  have hsingle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => (upperPeriodicBump_bounds η (θ j)).1)
    (Finset.mem_univ i)
  rw [hsum] at hsingle
  exact le_antisymm hsingle (upperPeriodicBump_bounds η (θ i)).1

theorem actualHomotopyAngle_of_upperPopulation_zero {N : ℕ} (hN : 0 < N)
    (η τ ξ : ℝ) (θ : Fin N → ℝ) (hP : actualUpperOccupancy η θ = 0) (i : Fin N) :
    actualHomotopyAngle η τ ξ θ i = (θ i : ℂ) := by
  rw [actualHomotopyAngle_eq_fixedOccupancy]
  have hp := upperBumps_zero_of_actualUpperOccupancy_zero hN η θ hP i
  simp only [fixedOccupancyAngle, hP, hp, zero_mul, mul_zero, sub_zero, Complex.ofReal_zero]

theorem exists_positive_angle_of_upperPopulation_pos {N : ℕ}
    (η : ℝ) (hη : 0 < η) (θ : Fin N → ℝ)
    (hθ : ∀ i, -Real.pi ≤ θ i) (hP : 0 < actualUpperOccupancy η θ) :
    ∃ i, 0 < θ i := by
  by_contra hnone
  push Not at hnone
  have hp : ∀ i, upperPeriodicBump η (θ i) = 0 := by
    intro i
    apply upperPeriodicBump_zero hη
    exact (Real.sin_nonpos_of_nonpos_of_neg_pi_le (hnone i) (hθ i)).trans hη.le
  simp only [actualUpperOccupancy, hp, Finset.sum_const_zero, zero_div] at hP
  exact lt_irrefl _ hP

theorem actual_upperPopulation_pos_scale_lower {N : ℕ} (hN : 0 < N)
    (b η ε r : ℝ) (hη : 0 < η) (hε : 0 ≤ ε)
    (θ : Fin N → ℝ) (hθ : ∀ i, -Real.pi ≤ θ i)
    (hdiam : ∀ i j, |θ i - θ j| ≤ 2 * r) (hP : 0 < actualUpperOccupancy η θ) :
    b / 2 ≤ |angularMean (fun k => θ k + b)| + r + ε := by
  obtain ⟨i, hi⟩ := exists_positive_angle_of_upperPopulation_pos η hη θ hθ hP
  have hm := angularMean_distance_bound hN (fun k => θ k + b) (2 * r)
    (fun j k => by simpa only [add_sub_add_right_eq_sub] using hdiam j k) i
  have hupper := (abs_le.mp hm).2
  have hμ := le_abs_self (angularMean (fun k => θ k + b))
  have ha := abs_nonneg (angularMean (fun k => θ k + b))
  linarith only [hi, hupper, hμ, ha, hε]

theorem actual_angular_sqrt_scale_bound {N : ℕ} (hN : 0 < N)
    (b ε r : ℝ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (θ : Fin N → ℝ)
    (hdiam : ∀ i j, |θ i - θ j| ≤ 2 * r) (i : Fin N) :
    Real.sqrt (|θ i + b| + ε) ≤
      2 * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) := by
  have hm := angularMean_distance_bound hN (fun k => θ k + b) (2 * r)
    (fun j k => by simpa only [add_sub_add_right_eq_sub] using hdiam j k) i
  have habs : |θ i + b| ≤ |angularMean (fun k => θ k + b)| + 2 * r := by
    have hh := abs_add_le ((θ i + b) - angularMean (fun k => θ k + b))
      (angularMean (fun k => θ k + b))
    rw [sub_add_cancel] at hh
    linarith only [hh, hm]
  have hT : 0 ≤ |angularMean (fun k => θ k + b)| + r + ε := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hT]
  norm_num
  linarith only [habs, hr, hε, abs_nonneg (angularMean (fun k => θ k + b))]

end IsingBulk.AnisoF002.Isotropic
