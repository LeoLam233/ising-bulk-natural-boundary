import Mathlib.Analysis.Real.Pi.Bounds
import IsingBulk.Anisotropic.NegativeDominance.EntropyCancellation
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform first-difference bounds for the exact Barnes/factorial entropy.
These supply the order-crossing argument without differentiating asymptotic errors. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem log_factorial_coarse (n : ℕ) (hn : 0 < n) :
    (n : ℝ)*Real.log n-n ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ (n : ℝ)*Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hpi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  constructor
  · have h := Stirling.le_log_factorial_stirling hn.ne'
    linarith
  · have h : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) h
    simpa only [Real.log_pow] using hh

theorem log_unit_increment (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.log (x+1)-Real.log x ∧
      x*(Real.log (x+1)-Real.log x) ≤ 1 := by
  have he : Real.log (x+1)-Real.log x = Real.log ((x+1)/x) :=
    (Real.log_div (by positivity) hx.ne').symm
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hx (by linarith))
  · rw [he]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x+1)/x by positivity)
    have hh := mul_le_mul_of_nonneg_left h hx.le
    field_simp at hh
    nlinarith

theorem particleLog_unit_bounds (x : ℝ) (hx : 2 ≤ x) :
    x*Real.log x ≤ particleLog (x+1)-particleLog x ∧
      particleLog (x+1)-particleLog x ≤ x*Real.log x+3*x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogupper : Real.log x ≤ x := le_trans (Real.log_le_sub_one_of_pos hx0) (by linarith)
  obtain ⟨hd0, hd1⟩ := log_unit_increment x hx0
  let d := Real.log (x+1)-Real.log x
  let A := (x+1)^2/2-1
  have hA : 0 ≤ A := by dsimp [A]; nlinarith
  have hAe : A ≤ 2*x^2 := by dsimp [A]; nlinarith
  have hd : 0 ≤ d := hd0
  have hxd : x*d ≤ 1 := hd1
  have hprod : A*d ≤ 2*x := by
    have h1 := mul_le_mul_of_nonneg_right hAe hd
    have h2 := mul_le_mul_of_nonneg_left hxd (show 0 ≤ 2*x by positivity)
    nlinarith
  have he : particleLog (x+1)-particleLog x = x*Real.log x+Real.log x/2+A*d := by
    dsimp [particleLog, A, d]
    ring
  rw [he]
  constructor
  · nlinarith [mul_nonneg hA hd]
  · linarith

theorem entropyPart_succ_bounds (n : ℕ) (hn : 2 ≤ n) :
    -5*(n : ℝ) ≤ entropyPart (n+1)-entropyPart n ∧
      entropyPart (n+1)-entropyPart n ≤ 0 := by
  obtain ⟨hfl, hfu⟩ := log_factorial_coarse n (by omega)
  obtain ⟨hpl, hpu⟩ := particleLog_unit_bounds n (by exact_mod_cast hn)
  have he := log_factorialProduct_succ n
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2u : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_left h2u hnn
  dsimp [entropyPart]
  push_cast
  constructor <;> nlinarith [mul_nonneg hnn h2]

theorem entropyPart_step_bounds (n d : ℕ) (hn : 2 ≤ n) :
    -5*(d : ℝ)*((n : ℝ)+d) ≤ entropyPart (n+d)-entropyPart n ∧
      entropyPart (n+d)-entropyPart n ≤ 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨hl, hu⟩ := entropyPart_succ_bounds (n+d) (by omega)
    rw [show n+d+1 = n+(d+1) by omega] at hl hu
    push_cast at hl hu ⊢
    constructor <;> nlinarith [ih.1, ih.2]

theorem entropyPart_step_abs_bound (n d : ℕ) (hn : 2 ≤ n) :
    |entropyPart (n+d)-entropyPart n| ≤ 5*(d : ℝ)*((n : ℝ)+d) := by
  obtain ⟨hl, hu⟩ := entropyPart_step_bounds n d hn
  rw [abs_of_nonpos hu]
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
