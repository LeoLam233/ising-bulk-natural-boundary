import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact Gamma ratios used by ANISO (5.24), (5.28) and (5.30).
The particle-dependent integer shift is never replaced by a fixed-index
asymptotic power. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- The positive rising product, with an arbitrary real initial argument. -/
def risingProduct (x : ℝ) (a : ℕ) : ℝ :=
  ∏ k ∈ Finset.range a, (x + k)

 theorem risingProduct_pos {x : ℝ} (hx : 0 < x) (a : ℕ) :
    0 < risingProduct x a := by
  apply Finset.prod_pos
  intro k _
  positivity

/-- Exact recurrence, for arbitrary integer shift, rather than a Stirling approximation. -/
theorem gamma_add_nat_eq_risingProduct {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Real.Gamma (x + a) = risingProduct x a * Real.Gamma x := by
  induction a with
  | zero => simp [risingProduct]
  | succ a ih =>
      have hp : 0 < x + a := by positivity
      rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hp.ne', ih]
      simp only [risingProduct, Finset.prod_range_succ]
      ring

/-- Exact Gamma quotient for every positive real base and every integer shift. -/
theorem gamma_ratio_eq_inv_risingProduct {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Real.Gamma x / Real.Gamma (x + a) = (risingProduct x a)⁻¹ := by
  rw [gamma_add_nat_eq_risingProduct hx]
  have hg := (Real.Gamma_pos_of_pos hx).ne'
  field_simp

/-- Exact logarithm of the Gamma quotient. The finite logarithmic sum is
retained at the growing shift used by the saddle selection. -/
theorem log_gamma_ratio_eq_sum {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Real.log (Real.Gamma x / Real.Gamma (x + a)) =
      -∑ k ∈ Finset.range a, Real.log (x + k) := by
  rw [gamma_ratio_eq_inv_risingProduct hx, Real.log_inv]
  congr 1
  exact Real.log_prod (fun k _ => (show 0 < x + k by positivity).ne')

/-- Specialization to the exact positive-argument quotient of (5.24). -/
theorem gamma_jet_ratio (a j : ℕ) (h : a ≤ j) :
    Real.Gamma ((j : ℝ) + 1 - a) / Real.Gamma ((j : ℝ) + 1) =
      (risingProduct ((j : ℝ) + 1 - a) a)⁻¹ := by
  have hcast : (a : ℝ) ≤ j := by exact_mod_cast h
  have hx : 0 < (j : ℝ) + 1 - a := by linarith
  have heq : (j : ℝ) + 1 - a + a = j + 1 := by ring
  simpa only [heq] using gamma_ratio_eq_inv_risingProduct hx a

/-- The exact descending-log formula used in (5.28), including its entire
finite correction. It holds for simultaneously growing `a` and `j`. -/
theorem log_gamma_jet_ratio (a j : ℕ) (h : a ≤ j) (hj : 0 < j) :
    Real.log (Real.Gamma ((j : ℝ) + 1 - a) / Real.Gamma ((j : ℝ) + 1)) =
      -(a : ℝ) * Real.log j -
        ∑ m ∈ Finset.range a, Real.log (1 - (m : ℝ) / j) := by
  have hcast : (a : ℝ) ≤ j := by exact_mod_cast h
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hx : 0 < (j : ℝ) + 1 - a := by linarith
  have heq : (j : ℝ) + 1 - a + a = j + 1 := by ring
  have hlog := log_gamma_ratio_eq_sum hx a
  rw [heq] at hlog
  rw [hlog, ← Finset.sum_range_reflect
    (fun k => Real.log ((j : ℝ) + 1 - a + k)) a]
  have hs : (∑ m ∈ Finset.range a,
      Real.log ((j : ℝ) + 1 - a + (a - 1 - m : ℕ))) =
      ∑ m ∈ Finset.range a, (Real.log j + Real.log (1 - (m : ℝ) / j)) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hma : m < a := Finset.mem_range.mp hm
    have hmj : (m : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le hma h)
    have hca : ((a - 1 - m : ℕ) : ℝ) = (a : ℝ) - 1 - m := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    rw [hca]
    have he : (j : ℝ) + 1 - a + ((a : ℝ) - 1 - m) =
        j * (1 - (m : ℝ) / j) := by field_simp; ring
    rw [he, Real.log_mul hjr.ne' (by
      have : (m : ℝ) / j < 1 := (div_lt_one hjr).mpr hmj
      linarith)]
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
