import IsingBulk.Tail.NatExponentialEnvelope
import IsingBulk.Tail.MicrocoreSummability

namespace IsingBulk.Tail
noncomputable section
open Filter

/-- Quadratic prefactors and a linear exponential collision-slope cost are
summable after the equality exponent is chosen. The threshold precedes that
choice, and all finite particle orders are covered by ordinary summability. -/
theorem collision_scale_summable {f h : ℕ → ℝ}
    (hf : NatExponentialEnvelope 2 f) (hh : NatExponentialEnvelope 1 h) (m : ℕ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      Summable (fun N : ℕ => f N*h N^(N*(N-1))*
        (4*Real.exp (-B*(N:ℝ)))^(N*(N-1)-m)) := by
  obtain ⟨Cf,hCf,hf⟩ := hf
  obtain ⟨Ch,hCh,hh⟩ := hh
  refine ⟨Ch+1,by positivity,?_⟩
  intro B hB
  have hBpos : 0 < B := by linarith
  have ha : 0 < B-Ch := by linarith
  let D := Cf+4+B+B*(m:ℝ)
  apply (microcore_cubic_summable D (B-Ch) ha).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (m+2)] with N hN
  have hN1 : 1 ≤ N := by omega
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN1
  have hNm : m ≤ N*(N-1) := by
    have he := Nat.sub_add_cancel hN1
    nlinarith
  have hP : N*(N-1) ≤ N^2 := by nlinarith [Nat.sub_le N 1]
  have hQ : N*(N-1)-m ≤ N^2 := (Nat.sub_le _ _).trans hP
  have hPcast : ((N*(N-1):ℕ):ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hP
  have hQcast : ((N*(N-1)-m:ℕ):ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hQ
  have hhN : |h N| ≤ Real.exp (Ch*(N:ℝ)) := by simpa only [pow_one] using hh N hN1
  have hhpow : |h N|^(N*(N-1)) ≤ Real.exp (Ch*(N:ℝ)^3) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) hhN _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hPcast (mul_nonneg hCh (Nat.cast_nonneg N))
    nlinarith
  have hfour : (4:ℝ)^(N*(N-1)-m) ≤ Real.exp (4*(N:ℝ)^2) := by
    have h4 : (4:ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
    apply (pow_le_pow_left₀ (by norm_num) h4 _).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnorm : ‖f N*h N^(N*(N-1))*(4*Real.exp (-B*(N:ℝ)))^(N*(N-1)-m)‖ ≤
      Real.exp ((Cf+4)*(N:ℝ)^2+Ch*(N:ℝ)^3-B*(N:ℝ)*((N*(N-1)-m:ℕ):ℝ)) := by
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_pow,abs_of_pos (by positivity : 0 < 4*Real.exp (-B*(N:ℝ))),
      mul_pow,← Real.exp_nat_mul]
    calc
      _ ≤ Real.exp (Cf*(N:ℝ)^2)*Real.exp (Ch*(N:ℝ)^3)*
          (Real.exp (4*(N:ℝ)^2)*Real.exp (((N*(N-1)-m:ℕ):ℝ)*(-B*(N:ℝ)))) := by
        gcongr
        exact hf N hN1
      _ = _ := by rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; congr 1; ring
  apply hnorm.trans
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub hNm,Nat.cast_mul,Nat.cast_sub hN1,Nat.cast_one]
  have hlin := mul_le_mul_of_nonneg_left (show (N:ℝ) ≤ (N:ℝ)^2 by nlinarith)
    (mul_nonneg hBpos.le (Nat.cast_nonneg m))
  dsimp [D]
  nlinarith [mul_nonneg ha.le (Nat.cast_nonneg N)]

end
end IsingBulk.Tail
