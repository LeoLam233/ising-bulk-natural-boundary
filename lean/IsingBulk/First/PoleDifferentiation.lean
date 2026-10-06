import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The exact high-order fixed-parameter derivative of a simple pole. All lower
pole orders are collected into a recursively constructed analytic remainder;
no derivative expansion or coefficient bound is assumed as data. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology

def poleLeadingNumerator (B D : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ)^k * (k.factorial : ℂ) * B s * (deriv D s)^k

def poleRemainder (B D : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | k+1 => fun s => deriv (poleLeadingNumerator B D k) s +
      D s * deriv (poleRemainder B D k) s - (k : ℂ)*deriv D s*poleRemainder B D k s

def poleCombinedNumerator (B D : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  poleLeadingNumerator B D k s + D s * poleRemainder B D k s

theorem poleLeadingNumerator_analyticAt {B D : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hD : AnalyticAt ℂ D s) (k : ℕ) :
    AnalyticAt ℂ (poleLeadingNumerator B D k) s := by
  have hd := hD.deriv
  unfold poleLeadingNumerator
  fun_prop

theorem poleRemainder_analyticAt {B D : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hD : AnalyticAt ℂ D s) (k : ℕ) :
    AnalyticAt ℂ (poleRemainder B D k) s := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih =>
    have hl := (poleLeadingNumerator_analyticAt hB hD k).deriv
    have hr := ih.deriv
    have hd := hD.deriv
    unfold poleRemainder
    exact hl.add (hD.mul hr) |>.sub (((analyticAt_const.mul hd).mul ih))

theorem poleLeadingNumerator_succ (B D : ℂ → ℂ) (k : ℕ) (s : ℂ) :
    poleLeadingNumerator B D (k+1) s =
      -((k+1 : ℕ) : ℂ)*deriv D s*poleLeadingNumerator B D k s := by
  simp only [poleLeadingNumerator, pow_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem poleCombinedNumerator_hasDerivAt {B D : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hD : AnalyticAt ℂ D s) (k : ℕ) :
    HasDerivAt (poleCombinedNumerator B D k)
      (deriv (poleLeadingNumerator B D k) s +
        deriv D s*poleRemainder B D k s + D s*deriv (poleRemainder B D k) s) s := by
  have hl := (poleLeadingNumerator_analyticAt hB hD k).differentiableAt.hasDerivAt
  have hr := (poleRemainder_analyticAt hB hD k).differentiableAt.hasDerivAt
  convert hl.add (hD.differentiableAt.hasDerivAt.mul hr) using 1
  · rfl
  · ring

theorem poleCombinedNumerator_succ (B D : ℂ → ℂ) (k : ℕ) (s : ℂ) :
    poleCombinedNumerator B D (k+1) s =
      D s*(deriv (poleLeadingNumerator B D k) s +
        deriv D s*poleRemainder B D k s + D s*deriv (poleRemainder B D k) s) -
        ((k+1 : ℕ) : ℂ)*deriv D s*poleCombinedNumerator B D k s := by
  simp only [poleCombinedNumerator, poleLeadingNumerator_succ, poleRemainder,
    Nat.cast_add, Nat.cast_one]
  ring

/-- Equality is localized on an actual open analytic domain before it is
differentiated. The denominator need be nonzero only at the evaluation point. -/
theorem iteratedDeriv_eq_poleCombinedNumerator {B D : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hB : AnalyticOnNhd ℂ B U) (hD : AnalyticOnNhd ℂ D U)
    (k : ℕ) {s : ℂ} (hs : s ∈ U) (hne : D s ≠ 0) :
    (deriv^[k] (fun z => B z / D z)) s =
      poleCombinedNumerator B D k s / (D s)^(k+1) := by
  induction k generalizing s with
  | zero => simp [poleCombinedNumerator, poleLeadingNumerator, poleRemainder]
  | succ k ih =>
    have he : (deriv^[k] (fun z => B z / D z)) =ᶠ[𝓝 s]
        (fun z => poleCombinedNumerator B D k z/(D z)^(k+1)) := by
      filter_upwards [hU.mem_nhds hs, (hD s hs).continuousAt.eventually_ne hne] with z hzu hzn
      exact ih hzu hzn
    have hp := (poleCombinedNumerator_hasDerivAt (hB s hs) (hD s hs) k).div
      ((hD s hs).differentiableAt.hasDerivAt.pow (k+1)) (pow_ne_zero _ hne)
    have hp' : HasDerivAt (fun z => poleCombinedNumerator B D k z/(D z)^(k+1))
        (poleCombinedNumerator B D (k+1) s/(D s)^(k+2)) s := by
      convert hp using 1
      rw [poleCombinedNumerator_succ]
      simp only [Pi.pow_apply, Nat.add_sub_cancel]
      field_simp [hne]
      simp only [pow_succ]
      ring
    rw [Function.iterate_succ', Function.comp_apply, he.deriv_eq, hp'.deriv]

/-- Source-faithful highest-pole term and a genuinely analytic lower-pole remainder. -/
theorem iteratedDeriv_simplePole_expansion {B D : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hB : AnalyticOnNhd ℂ B U) (hD : AnalyticOnNhd ℂ D U)
    (k : ℕ) {s : ℂ} (hs : s ∈ U) (hne : D s ≠ 0) :
    (deriv^[k] (fun z => B z / D z)) s =
      (-1 : ℂ)^k * (k.factorial : ℂ)*B s*(deriv D s)^k/(D s)^(k+1) +
        poleRemainder B D k s/(D s)^k := by
  rw [iteratedDeriv_eq_poleCombinedNumerator hU hB hD k hs hne]
  simp only [poleCombinedNumerator, poleLeadingNumerator]
  rw [pow_succ]
  field_simp

theorem poleRemainder_analyticOnNhd {B D : ℂ → ℂ} {U : Set ℂ}
    (hB : AnalyticOnNhd ℂ B U) (hD : AnalyticOnNhd ℂ D U) (k : ℕ) :
    AnalyticOnNhd ℂ (poleRemainder B D k) U :=
  fun s hs => poleRemainder_analyticAt (hB s hs) (hD s hs) k

/-- A fixed shape weight or Vandermonde is constant under parameter differentiation. -/
theorem iterate_deriv_const_mul (c : ℂ) (f : ℂ → ℂ) (k : ℕ) :
    deriv^[k] (fun s => c*f s) = fun s => c*(deriv^[k] f) s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply, ih, deriv_const_mul_field']

end
end IsingBulk.First
