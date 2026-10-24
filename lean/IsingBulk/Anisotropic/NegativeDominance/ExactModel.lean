import IsingBulk.Anisotropic.NegativeDominance.ExactGamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-! The exact first-winding model in ANISO (5.22)--(5.24). A square-root
value is an explicit argument: the physical branch is not silently replaced
by positivity or a phase common to different particle indices. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def alpha (n : ℕ) : ℕ := (n * n - 1) / 2

def tau (n : ℕ) : ℝ := 1 - Real.cos (Real.pi / n)

def factorialProduct (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.range n, (r.factorial : ℝ) / 2 ^ r

def hessianFactor (Bn : ℂ) (b s : ℝ) (n : ℕ) : ℂ :=
  (Real.cos (Real.pi / n) : ℂ) -
    Bn * b / (s : ℂ)^2 * (Real.sin (Real.pi / n) : ℂ)^2

/-- Exact complex coefficient (5.24). `rootBn` is the physical value of
`√B(τₙ)`; its branch and square identity are proved in the physical chart. -/
def model (Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ) : ℂ :=
  -(Real.rpow 2 (2 - (alpha n : ℝ)) : ℂ) * (Bn ^ alpha n / rootBn) *
    (factorialProduct n : ℂ) * (Real.rpow n ((alpha n : ℝ) - 3 / 2) : ℂ) /
    ((Real.rpow Real.pi (((n : ℝ) - 1) / 2) : ℂ) * (s : ℂ) ^ (2 * alpha n)) *
    hn ^ (-(alpha n : ℤ)) * (tau n : ℂ) ^ ((alpha n : ℤ) - j - 1) *
    (Real.Gamma ((j : ℝ) + 1 - alpha n) / Real.Gamma ((j : ℝ) + 1) : ℝ)

theorem factorialProduct_pos (n : ℕ) : 0 < factorialProduct n := by
  apply Finset.prod_pos
  intro r _
  exact div_pos (by positivity) (by positivity)

theorem factorialProduct_succ (n : ℕ) :
    factorialProduct (n + 1) = factorialProduct n * (n.factorial : ℝ) / 2 ^ n := by
  simp only [factorialProduct, Finset.prod_range_succ]
  ring

/-- The exact product is never zero, including all finite particle orders. -/
theorem factorialProduct_ne_zero (n : ℕ) : factorialProduct n ≠ 0 :=
  (factorialProduct_pos n).ne'

/-- The Gamma factor of the model is positive throughout its actual beta
convergence range. This does not assert a common phase for `model`. -/
theorem model_gamma_pos (n j : ℕ) (h : alpha n ≤ j) :
    0 < Real.Gamma ((j : ℝ) + 1 - alpha n) / Real.Gamma ((j : ℝ) + 1) := by
  have hc : (alpha n : ℝ) ≤ j := by exact_mod_cast h
  apply div_pos <;> apply Real.Gamma_pos_of_pos <;> linarith [show (0 : ℝ) ≤ j by positivity]

/-- Replacement by the finite reciprocal product is an equality, uniformly
for growing particle and derivative indices. -/
theorem model_exact_gamma_product (Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ)
    (h : alpha n ≤ j) :
    model Bn rootBn hn s n j =
      -(Real.rpow 2 (2 - (alpha n : ℝ)) : ℂ) * (Bn ^ alpha n / rootBn) *
      (factorialProduct n : ℂ) * (Real.rpow n ((alpha n : ℝ) - 3 / 2) : ℂ) /
      ((Real.rpow Real.pi (((n : ℝ) - 1) / 2) : ℂ) * (s : ℂ) ^ (2 * alpha n)) *
      hn ^ (-(alpha n : ℤ)) * (tau n : ℂ) ^ ((alpha n : ℤ) - j - 1) *
      ((risingProduct ((j : ℝ) + 1 - alpha n) (alpha n))⁻¹ : ℝ) := by
  unfold model
  rw [gamma_jet_ratio (alpha n) j h]

end
end IsingBulk.Anisotropic.NegativeDominance
