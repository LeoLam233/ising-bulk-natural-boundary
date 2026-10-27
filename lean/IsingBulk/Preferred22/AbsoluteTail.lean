import IsingBulk.Preferred22.Physical
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Preferred22: every-order numerical summation

These are the numerical summation obligations used after (8.10). No estimate
for the actual angular coefficients is assumed or declared here. The root-test
argument for the square-root envelope is adapted from the foundational
`Tail.ExteriorConvergenceBounds.sqrt_majorant_summable`, with no import of its
physical dependencies or of an older full-tail endpoint.
-/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped Topology BigOperators

/-- The integer-polynomial form of the all-order shell prefactor. -/
def shellOrderEnvelope (C : ℝ) (J N : ℕ) : ℝ :=
  (N : ℝ)^J * (C / Real.sqrt N)^N

/-- The exact exponent left after the coarea integration of §8. -/
def shellExponent (N j : ℕ) : ℝ := (N : ℝ) - 2 * (j : ℝ) - 3/2

/-- The stated cutoff leaves a uniform positive dyadic exponent. -/
theorem large_order_shell_exponent {N j k : ℕ} (hj : j ≤ k) (hN : 2*k+4 < N) :
    1 ≤ shellExponent N j := by
  unfold shellExponent
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hN' : 2 * (k : ℝ) + 5 ≤ N := by exact_mod_cast (show 2*k+5 ≤ N by omega)
  linarith

/-- At every higher even order the puncture flux has strictly positive degree
for all transports up through the first-singularity derivative order. -/
theorem higher_order_collision_degree {N Nstar j k : ℕ}
    (hNstar : 2 ≤ Nstar) (hN : Nstar+2 ≤ N)
    (hj : j ≤ k) (hk : 2*k+2 = Nstar^2) :
    0 < (N : ℤ)^2 - 2*(j : ℤ) - 3 := by
  have hn : (Nstar : ℤ)+2 ≤ N := by exact_mod_cast hN
  have hs : (2 : ℤ) ≤ Nstar := by exact_mod_cast hNstar
  have hj' : (j : ℤ) ≤ k := by exact_mod_cast hj
  have hk' : 2*(k : ℤ)+2 = (Nstar : ℤ)^2 := by exact_mod_cast hk
  nlinarith [sq_nonneg ((N : ℤ)-(Nstar : ℤ)-2)]

/-- A direct root comparison proves all-order summability for arbitrary C. -/
theorem sqrt_order_envelope_summable (C : ℝ) :
    Summable (fun N : ℕ => (C / Real.sqrt N)^N) := by
  have ht : Tendsto (fun N : ℕ => C / Real.sqrt N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))
  have he : ∀ᶠ N : ℕ in atTop, ‖C / Real.sqrt N‖ ≤ (1/2 : ℝ) := by
    have h := ht.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℝ)‖ < 1/2))
    exact h.mono (fun N hN => le_of_lt (by simpa using hN))
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [he] with N hN
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hN N

/-- A fixed polynomial cost is absorbed into the same explicit envelope with
C replaced by exp(1) C. -/
theorem shell_order_envelope_bound {C : ℝ} (hC : 0 ≤ C) (J N : ℕ) :
    shellOrderEnvelope C J N ≤
      (J.factorial : ℝ) * ((Real.exp 1 * C) / Real.sqrt N)^N := by
  have hp := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) J
  have hp' : (N : ℝ)^J ≤ (J.factorial : ℝ) * Real.exp (N : ℝ) := by
    have hf : (0 : ℝ) < J.factorial := by positivity
    have h := (div_le_iff₀ hf).mp hp
    simpa only [mul_comm] using h
  have he : Real.exp (N : ℝ) = (Real.exp 1)^N := by simp
  calc
    shellOrderEnvelope C J N ≤
        ((J.factorial : ℝ) * Real.exp (N : ℝ)) * (C / Real.sqrt N)^N :=
      mul_le_mul_of_nonneg_right hp' (by positivity)
    _ = _ := by
      rw [he]
      simp only [mul_div_assoc, mul_pow]
      ring

/-- The exact all-order polynomially corrected shell prefactor is summable. -/
theorem shell_order_envelope_summable {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (shellOrderEnvelope C J) := by
  apply ((sqrt_order_envelope_summable (Real.exp 1 * C)).mul_left
    (J.factorial : ℝ)).of_nonneg_of_le
  · intro N
    unfold shellOrderEnvelope
    positivity
  · exact shell_order_envelope_bound hC J

/-- In particular the entire subsequence of positive even orders converges. -/
theorem even_shell_order_envelope_summable {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    Summable (fun n : ℕ => shellOrderEnvelope C J (2*(n+1))) :=
  (shell_order_envelope_summable hC J).comp_injective (fun _ _ h => by omega)

/-- The all-order majorant has one finite bound valid for every finite window.
This is a numerical series theorem, not a bound on the Ising coefficients. -/
theorem even_shell_order_window_bound {C : ℝ} (hC : 0 ≤ C) (J : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℕ,
      ∑ n ∈ S, shellOrderEnvelope C J (2*(n+1)) ≤ B := by
  refine ⟨max 1 (∑' n, shellOrderEnvelope C J (2*(n+1))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro S
  exact (Summable.sum_le_tsum S
    (fun n _ => by unfold shellOrderEnvelope; positivity)
    (even_shell_order_envelope_summable hC J)).trans (le_max_right _ _)


/-- Exact correspondence between the numerical prefactor used here and the
rpow notation C^N N^(-N/2+J) in (8.10). -/
theorem shell_order_envelope_eq_rpow (C : ℝ) (J N : ℕ) (hN : 0 < N) :
    shellOrderEnvelope C J N =
      C^N * (N : ℝ)^(-(N : ℝ)/2 + (J : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (Real.sqrt (N : ℝ))^N = (N : ℝ)^((N : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    congr 1
    ring
  rw [shellOrderEnvelope, div_pow, hden,
    show -(N : ℝ)/2 + (J : ℝ) = -((N : ℝ)/2)+(J : ℝ) by ring,
    Real.rpow_add hN', Real.rpow_neg hN'.le, Real.rpow_natCast]
  ring

/-- The unreduced r,T powers from (8.10), including all r > 0, are bounded
by the stated single-diameter power using T ≥ r. -/
theorem every_diameter_shell_comparison {r T : ℝ} (hr : 0 < r)
    (hT : r ≤ T) {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    r^(2*(N : ℝ)-2*(j : ℝ)-3) * T^(-(N : ℝ)+3/2) ≤
      r^(shellExponent N j) := by
  have hexp : -(N : ℝ)+3/2 ≤ 0 := by
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hb := Real.rpow_le_rpow_of_nonpos hr hT hexp
  calc
    _ ≤ r^(2*(N : ℝ)-2*(j : ℝ)-3) * r^(-(N : ℝ)+3/2) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le _)
    _ = r^(shellExponent N j) := by
      rw [← Real.rpow_add hr]
      congr 1
      unfold shellExponent
      ring

/-- A dyadic shell with exponent at least one has a uniform geometric
majorant, independent of the exponent and hence of N. -/
theorem dyadic_shell_le_geometric {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    ((1/2 : ℝ)^m)^q ≤ (1/2 : ℝ)^m := by
  have hr : 0 < (1/2 : ℝ)^m := by positivity
  have hr1 : (1/2 : ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hq

/-- Dyadic summation is performed all the way down to zero diameter. -/
theorem dyadic_shell_summable {q : ℝ} (hq : 1 ≤ q) :
    Summable (fun m : ℕ => ((1/2 : ℝ)^m)^q) := by
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).of_nonneg_of_le
      (fun m => by positivity) (dyadic_shell_le_geometric hq)

/-- The logarithmic factor is strictly lower order than epsilon^(-1/2). -/
theorem logarithmic_factor_times_sqrt_tendsto_zero :
    Tendsto (fun eps : ℝ => Real.sqrt eps * (1+|Real.log eps|))
      (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun eps : ℝ => Real.log eps * Real.sqrt eps)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1/2)
  have h := hs.add hl.abs
  simp only [abs_zero, add_zero] at h
  convert h using 1
  funext eps
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg eps)]
  ring


/-- The true positive-even higher-order differentiated coefficient sequence.
This is the concrete sequence whose complete absolute sum is required in §9. -/
def actualHigherTailTerms (ζ : ℂ) (Nstar j : ℕ) (eps : ℝ) (n : ℕ) : ℝ :=
  if Nstar < 2*(n+1) then
    ‖iteratedDeriv j (coefficient (2*(n+1))) (((1+eps : ℝ) : ℂ)*ζ)‖
  else 0

/-- The actual infinite absolute tail; all positive even orders above Nstar
are included. Summability is a separate part of the required statement below. -/
def actualHigherTail (ζ : ℂ) (Nstar j : ℕ) (eps : ℝ) : ℝ :=
  ∑' n : ℕ, actualHigherTailTerms ζ Nstar j eps n

/-- UNPROVED source obligation: Theorem 9.1 for the actual coefficient from
Physical.lean. This declaration records a proposition only. None of the
numerical-envelope theorems above establishes or assumes this proposition. -/
def PreferredAbsoluteTailStatement (ζ : ℂ) (Nstar k : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ k → ∃ C eps0 : ℝ, 0 < C ∧ 0 < eps0 ∧
    ∀ eps : ℝ, 0 < eps → eps < eps0 →
      Summable (actualHigherTailTerms ζ Nstar j eps) ∧
      actualHigherTail ζ Nstar j eps ≤ C*(1+|Real.log eps|)

end
end IsingBulk.Preferred22
