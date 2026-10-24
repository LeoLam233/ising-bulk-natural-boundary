import IsingBulk.Tail.GlobalAnalytic

/-! Actual summability of the N log(N+1) loss in ANISO (3.6).
This is a scalar series theorem, not a bound assumed for the form factors. -/
namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Filter

/-- A tangent-line estimate absorbs the logarithm without differentiating an
asymptotic O-term. It applies to every nonnegative particle index. -/
theorem logarithm_linear_majorant {d : ℝ} (hd : 0 < d) (N : ℕ) :
    Real.log ((N:ℝ)+1) ≤ d*(N+1)-1-Real.log d := by
  have hx : 0 < (N:ℝ)+1 := by positivity
  have hh := Real.log_le_sub_one_of_pos (mul_pos hd hx)
  rw [Real.log_mul hd.ne' hx.ne'] at hh
  linarith

/-- The complete Gaussian envelope is summable with any fixed polynomial
loss, for all N, not merely along one parity or a finite particle window. -/
theorem gaussian_log_summable {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C) (j : ℕ) :
    Summable (fun N : ℕ => (N:ℝ)^j * Real.exp (-k*(N:ℝ)^2+C*N*Real.log ((N:ℝ)+1))) := by
  let d : ℝ := k/(2*(C+1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hde : 2*(C+1)*d=k := by dsimp [d]; field_simp
  have hCd : C*d ≤ k/2 := by nlinarith
  let a : ℝ := C*(d-1-Real.log d)
  apply (IsingBulk.Tail.summable_polynomial_gaussian a (by positivity : 0 < k/2) j).of_nonneg_of_le
    (fun N => by positivity)
  intro N
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hlog := logarithm_linear_majorant hd N
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC hn)
  have hq := mul_le_mul_of_nonneg_right hCd (sq_nonneg (N:ℝ))
  dsimp [a]
  nlinarith

/-- Norm domination then certifies a legitimate complex tsum before any
manipulation. The premise is a pointwise numerical bound, not convergence. -/
theorem summable_of_gaussian_log_bound {f : ℕ → ℂ} {k C : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (j : ℕ)
    (hf : ∀ N, ‖f N‖ ≤ (N:ℝ)^j * Real.exp (-k*(N:ℝ)^2+C*N*Real.log ((N:ℝ)+1))) :
    Summable f :=
  (gaussian_log_summable hk hC j).of_norm_bounded hf
end
end IsingBulk.Anisotropic.RegularEdges
