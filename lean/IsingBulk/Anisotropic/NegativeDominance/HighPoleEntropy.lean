import IsingBulk.Anisotropic.NegativeDominance.HighPoleIntegral

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- The explicit actual pole-integral envelope. -/
def highPoleEnvelope (M c : ℝ) (N j : ℕ) : ℝ :=
  (2*M^(1+alpha N+N+N.choose 2)/(c*N)*((N : ℝ)^2/2)^(j+1))*
    Real.exp (-(N : ℝ)^2/2*Real.log N+10*(N : ℝ)^2)

/-- Exact entropy strength of the full-dimensional high-range envelope,
valid for every Taylor order, including orders outside the beta range. -/
theorem highPoleEnvelope_entropy (M c : ℝ) (hM : 1≤M) (hc : 0<c) :
    ∃C : ℝ,0<C ∧ ∀N : ℕ,2≤N → ∀j : ℕ,
      highPoleEnvelope M c N j≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2) := by
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hlM : 0≤Real.log M := Real.log_nonneg hM
  refine ⟨11+3*Real.log M+|Real.log c|,by positivity,?_⟩
  intro N hN j
  have hNR : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have haNat : alpha N≤N*N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have ha : (alpha N : ℝ)≤(N : ℝ)^2 := by exact_mod_cast (show alpha N≤N^2 by simpa only [pow_two] using haNat)
  have hchoose := Nat.cast_choose_two (K := ℝ) N
  have he : ((1+alpha N+N+N.choose 2 : ℕ) : ℝ)≤3*(N : ℝ)^2 := by
    push_cast
    nlinarith only [ha,hchoose,hNR]
  have heM := mul_le_mul_of_nonneg_right he hlM
  have hlN : Real.log (N : ℝ)≤(N : ℝ)^2 := by
    have hh := Real.log_le_sub_one_of_pos hNp
    nlinarith only [hh,hNR]
  have hlc : -Real.log c≤|Real.log c| *(N : ℝ)^2 :=
    (neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) (by nlinarith only [hNR]))
  have hj : 0≤(j : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  apply (Real.log_le_iff_le_exp (by unfold highPoleEnvelope; positivity)).mp
  unfold highPoleEnvelope
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity),Real.log_pow,
    Real.log_mul hc.ne' hNp.ne',Real.log_pow,Real.log_div (by positivity) (by norm_num),Real.log_pow]
  push_cast
  push_cast at heM
  nlinarith only [heM,hlN,hlc,hj]

end
end IsingBulk.Anisotropic.NegativeDominance
