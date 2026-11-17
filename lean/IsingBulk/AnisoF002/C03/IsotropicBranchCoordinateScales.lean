import IsingBulk.AnisoF002.C03.IsotropicBranchIntegral

/-!
# Sharp branch shell differences of the physical regular coordinate

The difference estimate integrates the actual coordinate derivative
along a common outward contour. The scale is exactly the frozen
r/sqrt(|mu|+r+epsilon); it is only an envelope and is never differentiated.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem norm_sub_le_branch_shell_of_le {f d : ℝ → ℂ} {a b μ r ε C : ℝ}
    (hab : a ≤ b) (hr : 0 < r) (hε : 0 < ε) (hC : 0 ≤ C)
    (ha : μ - 2 * r ≤ a) (hb : b ≤ μ + 2 * r)
    (hd : ∀ u ∈ Icc a b, HasDerivAt f (d u) u ∧ ‖d u‖ ≤ C / Real.sqrt (|u| + ε)) :
    ‖f b - f a‖ ≤ 24 * C * r / Real.sqrt (|μ| + r + ε) := by
  have hint (x y : ℝ) : IntervalIntegrable (fun u => C * branchWeight ε u) volume x y :=
    ((branchWeight_continuous hε).const_mul C).intervalIntegrable x y
  have hh : ‖f b - f a‖ ≤ ∫ u in a..b, C * branchWeight ε u := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hab
    · intro u hu
      exact (hd u hu).1.continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u ⟨hu.1.le, hu.2.le⟩).1.differentiableAt.differentiableWithinAt
    · apply Filter.Eventually.of_forall
      intro u hu
      rw [(hd u ⟨hu.1.le, hu.2.le⟩).1.deriv]
      simpa only [branchWeight, mul_one_div] using (hd u ⟨hu.1.le, hu.2.le⟩).2
    · exact hint a b
  have hmono := intervalIntegral.integral_mono_interval ha hab hb
    (Filter.Eventually.of_forall (fun u => mul_nonneg hC (branchWeight_nonneg ε u)))
    (hint (μ - 2 * r) (μ + 2 * r))
  apply (hh.trans hmono).trans
  rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ C * (24 * r / Real.sqrt (|μ| + r + ε)) :=
      mul_le_mul_of_nonneg_left (branchWeight_shell_integral_bound μ r ε hr hε) hC
    _ = _ := by ring

/-- Sharp shell differences for the actual physical regular coordinate,
uniform in every common outward displacement in the fixed branch window. -/
theorem exists_branch_coordinate_shell_difference (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ R → ∀ h ∈ Icc 0 R,
      ∀ μ r : ℝ, 0 < r → ∀ u v : ℝ, |u| ≤ R → |v| ≤ R →
        u ∈ Icc (μ - 2 * r) (μ + 2 * r) →
        v ∈ Icc (μ - 2 * r) (μ + 2 * r) →
        ‖branchRegularCurve α b ε h u - branchRegularCurve α b ε h v‖ ≤
          C * r / Real.sqrt (|μ| + r + ε) := by
  obtain ⟨R, K, hR, hR1, hK, hd⟩ :=
    exists_branch_coordinate_derivative_majorant α b hα hb hpoint
  refine ⟨R, 24 * K, hR, hR1, by positivity, ?_⟩
  intro ε hε hεR h hh μ r hr u v hu hv hus hvs
  have hord (x y : ℝ) (hxy : x ≤ y) (hx : |x| ≤ R) (hy : |y| ≤ R)
      (hxs : x ∈ Icc (μ - 2 * r) (μ + 2 * r))
      (hys : y ∈ Icc (μ - 2 * r) (μ + 2 * r)) :
      ‖branchRegularCurve α b ε h y - branchRegularCurve α b ε h x‖ ≤
        24 * K * r / Real.sqrt (|μ| + r + ε) := by
    apply norm_sub_le_branch_shell_of_le hxy hr hε hK.le hxs.1 hys.2
    intro z hz
    apply hd ε hε hεR h hh z
    exact abs_le.mpr ⟨(abs_le.mp hx).1.trans hz.1, hz.2.trans (abs_le.mp hy).2⟩
  rcases le_total u v with huv | hvu
  · simpa only [norm_sub_rev] using hord u v huv hu hv hus hvs
  · exact hord v u hvu hv hu hvs hus

def angularMean {N : ℕ} (u : Fin N → ℝ) : ℝ := (∑ i, u i) / N

/-- A genuine diameter bound gives the shell interval around the actual
angular mean, with no selection of a distinguished particle. -/
theorem angularMean_distance_bound {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ)
    (D : ℝ) (hD : ∀ i j, |u i - u j| ≤ D) (i : Fin N) :
    |u i - angularMean u| ≤ D := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : u i - angularMean u = (∑ j, (u i - u j)) / N := by
    simp only [angularMean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ j, |u i - u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, D := Finset.sum_le_sum (fun j _ => hD i j)
    _ = D * N := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

end IsingBulk.AnisoF002.Isotropic
