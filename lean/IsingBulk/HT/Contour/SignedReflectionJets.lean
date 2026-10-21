import IsingBulk.HT.Contour.SignedReflection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Parameter derivatives of the exact reflected physical source. The radius
is held fixed, and reflection is applied to germs before taking derivatives. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Filter
open scoped Topology

 theorem iteratedDeriv_star_conj (j : ℕ) (F : ℂ → ℂ) :
    iteratedDeriv j (star ∘ F ∘ star) = star ∘ iteratedDeriv j F ∘ star := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
    change deriv (star ∘ iteratedDeriv j F ∘ (starRingEnd ℂ)) =
      star ∘ deriv (iteratedDeriv j F) ∘ (starRingEnd ℂ)
    exact deriv_star_conj

 theorem iteratedDeriv_star_neg_conj (j : ℕ) (F : ℂ → ℂ) (s : ℂ) :
    iteratedDeriv j (fun z => star (F (-star z))) s =
      (-1:ℂ)^j*star (iteratedDeriv j F (-star s)) := by
  have hh := congrFun (iteratedDeriv_star_conj j (fun z => F (-z))) s
  simpa only [Function.comp_def,iteratedDeriv_comp_neg,smul_eq_mul,
    star_mul',star_pow,star_neg,star_one] using hh

/-- Exact reflected derivative identity for the original offsite coefficient,
not an independently supplied reflected coefficient sequence. -/
theorem signedSourceIntegral_reflected_odd_iteratedDeriv
    (N : ℕ) (hN : Odd N) (hNpos : 0 < N) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) (hr : 0 < r) (hr1 : r < 1) (hm : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (signedSourceIntegral (-1) N r) s =
      (-1:ℂ)^j*star (iteratedDeriv j (upperFormFactor N) (-star s)) := by
  have hs := dampingDomain_of_margin hr hr1 hm
  have he : signedSourceIntegral (-1) N r =ᶠ[𝓝 s]
      (fun z => star (upperFormFactor N (-star z))) := by
    filter_upwards [dampingDomain_mem_nhds hs] with z hz
    have hh := congrArg star (upperFormFactor_reflected_odd_eq_signed N hN hNpos f r τ z hr hr1 hz.2)
    simpa only [star_star] using hh.symm
  rw [he.iteratedDeriv_eq j,iteratedDeriv_star_neg_conj]

/-- Every reflected derivative has exactly the signed-source norm, so the
complete signed tail bounds transfer without an extra particle-dependent cost. -/
theorem upperFormFactor_reflected_odd_iteratedDeriv_norm
    (N : ℕ) (hN : Odd N) (hNpos : 0 < N) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) (hr : 0 < r) (hr1 : r < 1) (hm : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    ‖iteratedDeriv j (upperFormFactor N) (-star s)‖ =
      ‖iteratedDeriv j (signedSourceIntegral (-1) N r) s‖ := by
  rw [signedSourceIntegral_reflected_odd_iteratedDeriv N hN hNpos f r τ s hr hr1 hm j]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,norm_star,one_mul]

/-- Reflection preserves the radial epsilon path, with acute angle θ mapped
exactly to the negative-upper angle π−θ. -/
theorem radialParameter_neg_conjugate (θ ε : ℝ) :
    radialParameter (Real.pi-θ) ε = -star (radialParameter θ ε) := by
  apply Complex.ext <;>
    simp [radialParameter,Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,
      Real.cos_pi_sub,Real.sin_pi_sub]

 theorem upperFormFactor_reflected_radial_odd_iteratedDeriv_norm
    (N : ℕ) (hN : Odd N) (hNpos : 0 < N) (f : SelectorFunctions)
    (r τ θ ε : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hm : r⁻¹-r < (sourceS (radialParameter θ ε)).im) (j : ℕ) :
    ‖iteratedDeriv j (upperFormFactor N) (radialParameter (Real.pi-θ) ε)‖ =
      ‖iteratedDeriv j (signedSourceIntegral (-1) N r) (radialParameter θ ε)‖ := by
  rw [radialParameter_neg_conjugate]
  exact upperFormFactor_reflected_odd_iteratedDeriv_norm N hN hNpos f r τ
    (radialParameter θ ε) hr hr1 hm j

end
end IsingBulk.HT.Contour
