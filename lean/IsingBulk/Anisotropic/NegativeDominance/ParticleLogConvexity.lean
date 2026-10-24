import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! Strong convexity of the exact quadratic logarithmic factor which
cancels the factorial-product entropy in the model. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set

def particleLog (x : ℝ) : ℝ := (x^2 / 2 - 1) * Real.log x
def particleLogD (x : ℝ) : ℝ := x * Real.log x + x / 2 - x⁻¹
def particleLogDD (x : ℝ) : ℝ := Real.log x + 3 / 2 + (x^2)⁻¹

theorem hasDerivAt_particleLog (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt particleLog (particleLogD x) x := by
  have hh := ((((hasDerivAt_id x).pow 2).div_const 2).sub_const 1).mul (Real.hasDerivAt_log hx)
  convert hh using 1
  · rfl
  · dsimp [particleLogD]
    field_simp
    ring

theorem hasDerivAt_particleLogD (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt particleLogD (particleLogDD x) x := by
  have hh := (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx)).add
    ((hasDerivAt_id x).div_const 2)).sub (hasDerivAt_inv hx)
  convert hh using 1
  · rfl
  · dsimp [particleLogDD]
    field_simp
    ring

/-- Subtracting the lower quadratic curvature leaves a convex function. -/
theorem convexOn_particleLog_sub_quadratic (L : ℝ) (hL : 0 < L) :
    ConvexOn ℝ (Ici L) (fun x => particleLog x - (Real.log L / 2) * x^2) := by
  have hp (x : ℝ) (hx : x ∈ Ici L) : 0 < x := lt_of_lt_of_le hL hx
  have hd (x : ℝ) (hx : x ∈ Ici L) :
      HasDerivAt (fun x => particleLog x - (Real.log L / 2) * x^2)
        (particleLogD x - Real.log L * x) x := by
    convert (hasDerivAt_particleLog x (hp x hx).ne').sub
      (((hasDerivAt_id x).pow 2).const_mul (Real.log L / 2)) using 1
    · rfl
    · dsimp; ring
  have hdd (x : ℝ) (hx : x ∈ Ici L) :
      HasDerivAt (fun x => particleLogD x - Real.log L * x)
        (particleLogDD x - Real.log L) x := by
    convert (hasDerivAt_particleLogD x (hp x hx).ne').sub
      ((hasDerivAt_id x).const_mul (Real.log L)) using 1
    · rfl
    · simp
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun x => particleLogD x - Real.log L * x)
    (f'' := fun x => particleLogDD x - Real.log L) (convex_Ici _)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => (hdd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hlog := Real.log_le_log hL (interior_subset hx : L ≤ x)
    dsimp [particleLogDD]
    have hsq : 0 ≤ (x^2)⁻¹ := by positivity
    linarith

theorem particleLog_second_difference_lower {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) :
    d^2 * Real.log x ≤ particleLog (x + 2 * d) - 2 * particleLog (x + d) + particleLog x := by
  have hc := convexOn_particleLog_sub_quadratic x hx
  have hm := hc.2 (show x ∈ Ici x by simp)
    (show x + 2 * d ∈ Ici x by simp only [mem_Ici]; linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (x + 2 * d) = x + d := by
    simp only [smul_eq_mul]; ring
  rw [hmid] at hm
  simp only [smul_eq_mul] at hm
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
