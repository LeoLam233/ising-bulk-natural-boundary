import IsingBulk.Anisotropic.NegativeNormalForm.BetaPeriod
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Polynomial MeasureTheory Set

/-- An actual polynomial primitive, avoiding any logarithmic branch in the
integer beta period. -/
theorem polynomial_exists_primitive (p : Polynomial ℂ) : ∃ P : Polynomial ℂ, P.derivative=p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P,hP⟩ := hp
    obtain ⟨Q,hQ⟩ := hq
    exact ⟨P+Q,by simp [hP,hQ]⟩
  | monomial n a =>
    refine ⟨Polynomial.monomial (n+1) (a/(n+1)),?_⟩
    simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel]
    congr 1
    have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show n+1≠0 by omega)
    push_cast
    field_simp

def complexBetaMobius (h z : ℂ) : ℂ := h*z/(1+(h-1)*z)

theorem complexBetaMobius_den_ne (h : ℂ) (hh : 0<h.re) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    1+(h-1)*(x:ℂ)≠0 := by
  have hr : 0<(1+(h-1)*(x:ℂ)).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.sub_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rcases lt_or_eq_of_le hx.2 with hx1 | rfl
    · nlinarith [mul_nonneg hh.le hx.1]
    · simpa using hh
  intro he
  rw [he,Complex.zero_re] at hr
  exact (lt_irrefl 0) hr

theorem complexBetaMobius_hasDerivAt (h z : ℂ) (hz : 1+(h-1)*z≠0) :
    HasDerivAt (complexBetaMobius h) (h/(1+(h-1)*z)^2) z := by
  have hd := ((hasDerivAt_id z).const_mul h).div
    ((hasDerivAt_const z (1:ℂ)).add ((hasDerivAt_id z).const_mul (h-1))) hz
  convert hd using 1
  · rfl
  · dsimp
    ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
