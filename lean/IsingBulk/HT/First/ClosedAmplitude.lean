import IsingBulk.HT.First.OrderArithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
The literal HT-1.0 closed first-chart amplitude, with its positivity and phase.
This file proves the algebraic nonvanishing of the manuscript formula. It does
not assert that the actual first contour derivative has this coefficient;
that separate localization, odd radial integral, and Gaussian normalization
identification must be supplied before the physical FIRST endpoint is closed.
-/
namespace IsingBulk.HT.First
noncomputable section
open scoped BigOperators Topology
open Filter

/-- P_p = product from m=1 to p−1 of m!/2^m. -/
def factorialAmplitudeProduct (p : ℕ) : ℝ :=
  ∏ m ∈ Finset.Icc 1 (p-1), (m.factorial : ℝ)/2^m

theorem factorialAmplitudeProduct_pos (p : ℕ) :
    0 < factorialAmplitudeProduct p := by
  unfold factorialAmplitudeProduct
  apply Finset.prod_pos
  intro m _hm
  positivity

/-- H_{αβ} in the frozen manuscript, without a sign restriction. -/
def curvatureNumerator (alpha beta : ℝ) : ℝ :=
  (Real.cos alpha+Real.cos beta)*(1-Real.cos alpha*Real.cos beta)

/-- The real positive magnitude B_*; for odd p, the π exponent is the
integer (p−1)/2, exactly as in the manuscript. -/
def closedAmplitudeMagnitude (p : ℕ) (theta H : ℝ) : ℝ :=
  factorialAmplitudeProduct p * ((p:ℝ)*Real.sin theta)^(derivativeOrder p-1) /
    (Real.sqrt (p:ℝ) * Real.pi^((p-1)/2) * |H|^(derivativeOrder p))

/-- L_* = −i exp(−ikθ) B_*. -/
def closedLeadingCoefficient (p : ℕ) (theta H : ℝ) : ℂ :=
  -Complex.I * Complex.exp (-Complex.I*(derivativeOrder p:ℂ)*(theta:ℂ)) *
    (closedAmplitudeMagnitude p theta H : ℂ)

theorem closedAmplitudeMagnitude_pos {p : ℕ} (hp : 0 < p)
    {theta H : ℝ} (htheta : 0 < Real.sin theta) (hH : H ≠ 0) :
    0 < closedAmplitudeMagnitude p theta H := by
  have hP := factorialAmplitudeProduct_pos p
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have hHpos : 0 < |H| := abs_pos.mpr hH
  unfold closedAmplitudeMagnitude
  positivity

theorem closedLeadingCoefficient_ne_zero {p : ℕ} (hp : 0 < p)
    {theta H : ℝ} (htheta : 0 < Real.sin theta) (hH : H ≠ 0) :
    closedLeadingCoefficient p theta H ≠ 0 := by
  unfold closedLeadingCoefficient
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.exp_ne_zero _))
    (Complex.ofReal_ne_zero.mpr (closedAmplitudeMagnitude_pos hp htheta hH).ne')

/-- Exchanging the two ordered charts preserves the exact closed coefficient. -/
theorem closedLeadingCoefficient_swap (p : ℕ) (theta alpha beta : ℝ) :
    closedLeadingCoefficient p theta (curvatureNumerator beta alpha) =
      closedLeadingCoefficient p theta (curvatureNumerator alpha beta) := by
  congr 1
  unfold curvatureNumerator
  ring

theorem four_closedLeadingCoefficient_ne_zero {p : ℕ} (hp : 0 < p)
    {theta H : ℝ} (htheta : 0 < Real.sin theta) (hH : H ≠ 0) :
    4*closedLeadingCoefficient p theta H ≠ 0 :=
  mul_ne_zero (by norm_num) (closedLeadingCoefficient_ne_zero hp htheta hH)

/-- Explicit algebraic assembly of the factor four. This transport lemma
has its first-chart and onsite limits as visible premises; it is not a proof
of those analytic limits or a substitute for the actual FIRST endpoint. -/
theorem onsite_offsite_scaled_limit {F T : ℝ → ℂ} {L : ℂ}
    (hF : Tendsto (fun ε : ℝ => (ε:ℂ)*F ε) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hT : Tendsto (fun ε : ℝ => (ε:ℂ)*T ε) (𝓝[>] (0:ℝ)) (𝓝 (2*L))) :
    Tendsto (fun ε : ℝ => (ε:ℂ)*(F ε+2*T ε)) (𝓝[>] (0:ℝ)) (𝓝 (4*L)) := by
  have h := hF.add (hT.const_mul 2)
  have hf : (fun ε : ℝ => (ε:ℂ)*(F ε+2*T ε)) =
      (fun ε : ℝ => (ε:ℂ)*F ε+2*((ε:ℂ)*T ε)) := by
    funext ε
    ring
  have hv : (0:ℂ)+2*(2*L) = 4*L := by ring
  rw [hf]
  simpa only [hv] using h

end
end IsingBulk.HT.First
