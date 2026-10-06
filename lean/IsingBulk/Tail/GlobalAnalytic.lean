import IsingBulk.First.DominatedAnalyticIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Analytic and summation substeps for large-current and high-order sectors.
Disk estimates are explicit premises here; none of these transfer lemmas is
claimed as a source sector proposition or an external Ising input. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

/-- Cauchy applies to a genuine continuation of the radial germ. This avoids
the invalid shortcut of evaluating the principal root on an enlarged disk. -/
theorem cauchy_bound_of_continued_germ {f g : ℂ → ℂ} {U : Set ℂ}
    {s : ℂ} (hfg : f =ᶠ[𝓝 s] g) (hg : ∀ z ∈ U, AnalyticAt ℂ g z)
    {B : ℝ} (hB : ∀ z ∈ U, ‖g z‖ ≤ B) {d : ℝ} (hd : 0 < d)
    (hsub : closedBall s d ⊆ U) (j : ℕ) :
    ‖iteratedDeriv j f s‖ ≤ j.factorial*B/d^j := by
  rw [hfg.iteratedDeriv_eq j]
  exact IsingBulk.First.cauchy_bound_on_subdisk hg hB hd hsub j

/-- Exact inverse-square integration is the source's stronger lambda*^(-j-1)
bound, before weakening to lambda*^(-j-2). -/
theorem integral_inverse_square {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : ℝ in a..1, x⁻¹^2) = a⁻¹-1 := by
  have hz (x : ℝ) (hx : x ∈ uIcc a 1) : x ≠ 0 := by
    rw [uIcc_of_le ha1] at hx
    exact (ha.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x : ℝ => x⁻¹^2) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_id.inv₀ hz).pow 2
  have hd (x : ℝ) (hx : x ∈ uIcc a 1) :
      HasDerivAt (fun y : ℝ => -y⁻¹) (x⁻¹^2) x := by
    convert! ((hasDerivAt_id x).inv (hz x hx)).neg using 1; simp [div_eq_mul_inv]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa [sub_eq_add_neg,add_comm] using h

/-- No integrability of the current is silently presumed in the majorization
step; the dominating inverse square is explicitly integrable. -/
theorem norm_large_current_integral_le {f : ℝ → ℂ} {a B : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Ioc a 1, ‖f x‖ ≤ B*x⁻¹^2) :
    ‖∫ x : ℝ in a..1, f x‖ ≤ B*a⁻¹ := by
  have hz (x : ℝ) (hx : x ∈ uIcc a 1) : x ≠ 0 := by
    rw [uIcc_of_le ha1] at hx
    exact (ha.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x : ℝ => B*x⁻¹^2) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul ((continuousOn_id.inv₀ hz).pow 2)
  calc
    _ ≤ ∫ x : ℝ in a..1, B*x⁻¹^2 :=
      intervalIntegral.norm_integral_le_of_norm_le ha1 (Filter.Eventually.of_forall hbound) hi
    _ = B*(a⁻¹-1) := by rw [intervalIntegral.integral_const_mul, integral_inverse_square ha ha1]
    _ ≤ B*a⁻¹ := by nlinarith

/-- Uniformity in lambda*: the N-series depends only on fixed derivative
order and fixed geometric constants. Completing a square controls all N,
including finitely many small orders. -/
theorem summable_polynomial_gaussian (a : ℝ) {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Summable (fun N : ℕ => (N:ℝ)^m*Real.exp (a*N-b*(N:ℝ)^2)) := by
  let C := (a+1)^2/(4*b)
  have hC : 4*b*C = (a+1)^2 := by dsimp [C]; field_simp
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul m (by norm_num : (0:ℝ)<1)).mul_left (Real.exp C)
  apply hbase.of_nonneg_of_le (fun N => by positivity)
  intro N
  have hquad : a*(N:ℝ)-b*(N:ℝ)^2 ≤ C-(N:ℝ) := by
    nlinarith [sq_nonneg (2*b*(N:ℝ)-(a+1))]
  calc
    _ ≤ (N:ℝ)^m*Real.exp (C-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) (by positivity)
    _ = Real.exp C*((N:ℝ)^m*Real.exp (-1*(N:ℝ))) := by
      rw [sub_eq_add_neg,Real.exp_add]
      ring

/-- The precise exponential-polynomial series used by the large-current
Cauchy bound, with C and kappa chosen before N and epsilon. -/
theorem summable_source_gaussian {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (m : ℕ) :
    Summable (fun N : ℕ => C^N*(N:ℝ)^m*Real.exp (-b*(N:ℝ)^2)) := by
  apply (summable_polynomial_gaussian C hb m).of_nonneg_of_le (fun N => by positivity)
  intro N
  have he : C ≤ Real.exp C := by linarith [Real.add_one_le_exp C]
  have hp : C^N ≤ Real.exp (C*(N:ℝ)) := by
    have h := pow_le_pow_left₀ hC he N
    simpa only [← Real.exp_nat_mul, mul_comm] using h
  calc
    _ ≤ Real.exp (C*(N:ℝ))*(N:ℝ)^m*Real.exp (-b*(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (Real.exp_pos _).le
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring

end
end IsingBulk.Tail
