import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic

/-! Local identities extracted directly from the dispersion relation.
No use is made of the unformalized original-disk lemma. Square-root estimates
below concern the designated lower-half-plane model, not yet arccos W. -/
namespace IsingBulk.Branch
noncomputable section

def dispersion (s y : ℂ) : ℂ := s+s⁻¹-(y+y⁻¹)/2

theorem polar_dispersion (s : ℂ) (v θ : ℝ) :
    dispersion s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I)) =
      s+s⁻¹-Complex.cosh ((v:ℂ)+(θ:ℂ)*Complex.I) := by
  simp only [dispersion, Complex.cosh]
  rw [← Complex.exp_neg]

theorem polar_dispersion_re (s : ℂ) (v θ : ℝ) :
    (dispersion s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))).re =
      (s+s⁻¹).re-Real.cosh v*Real.cos θ := by
  rw [polar_dispersion, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem polar_dispersion_im (s : ℂ) (v θ : ℝ) :
    (dispersion s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))).im =
      (s+s⁻¹).im-Real.sinh v*Real.sin θ := by
  rw [polar_dispersion, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

def plateauY (c₀ ε τ t θB u : ℝ) : ℂ :=
  Complex.exp (((-c₀*ε+τ*t/2 : ℝ):ℂ)+((-θB+u:ℝ):ℂ)*Complex.I)

theorem plateau_dispersion_components (s : ℂ) (c₀ ε τ t θB u : ℝ) :
    (dispersion s (plateauY c₀ ε τ t θB u)).re =
      (s+s⁻¹).re-Real.cosh (-c₀*ε+τ*t/2)*Real.cos (-θB+u) ∧
    (dispersion s (plateauY c₀ ε τ t θB u)).im =
      (s+s⁻¹).im-Real.sinh (-c₀*ε+τ*t/2)*Real.sin (-θB+u) :=
  ⟨polar_dispersion_re _ _ _, polar_dispersion_im _ _ _⟩

/-- The manuscript's Q and E are comparable with constants depending only on τ. -/
theorem plateau_scales (τ ε t : ℝ) (hτ : 0 < τ) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    0 < min 1 τ ∧
    min 1 τ * (ε+t) ≤ ε+τ*t ∧ ε+τ*t ≤ max 1 τ * (ε+t) := by
  refine ⟨lt_min (by norm_num) hτ, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) τ) hε
    have h₂ := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) τ) ht
    nlinarith
  · have h₁ := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) τ) hε
    have h₂ := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) τ) ht
    nlinarith

theorem sqrt_lower_components (D : ℂ) (him : D.im < 0) :
    (Complex.sqrt D).re = Real.sqrt ((‖D‖+D.re)/2) ∧
    -(Complex.sqrt D).im = Real.sqrt ((‖D‖-D.re)/2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [not_le.mpr him]

theorem sqrt_lower_orientation (D : ℂ) (him : D.im < 0) :
    0 < (Complex.sqrt D).re ∧ (Complex.sqrt D).im < 0 := by
  obtain ⟨hr, hi⟩ := sqrt_lower_components D him
  have hn : D.re^2+D.im^2 = ‖D‖^2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq D)
  have hnorm := norm_nonneg D
  have him2 : 0 < D.im^2 := sq_pos_of_neg him
  have hre := Complex.abs_re_le_norm D
  have ha : 0 < ‖D‖+D.re := by
    have := (abs_le.mp hre).1
    nlinarith
  have hb : 0 < ‖D‖-D.re := by
    have := (abs_le.mp hre).2
    nlinarith
  constructor
  · rw [hr]; exact Real.sqrt_pos.2 (by linarith)
  · have hp := Real.sqrt_pos.2 (show 0 < (‖D‖-D.re)/2 by linarith)
    linarith

/-- Exact lower-half-plane model attenuation. Passing through the analytic
factor h(D) is a separate source obligation. -/
theorem sqrt_negative_attenuation (D : ℂ) (him : D.im < 0) (hre : D.re ≤ 0) :
    Real.sqrt (‖D‖/2) ≤ -(Complex.sqrt D).im := by
  rw [(sqrt_lower_components D him).2]
  exact Real.sqrt_le_sqrt (by linarith)

theorem sqrt_positive_cone (D : ℂ) (him : D.im < 0) (hre : 0 ≤ D.re) :
    -(Complex.sqrt D).im ≤ (Complex.sqrt D).re := by
  rw [(sqrt_lower_components D him).1, (sqrt_lower_components D him).2]
  exact Real.sqrt_le_sqrt (by linarith)

end
end IsingBulk.Branch
