import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact all-order factorial summation for the integrated selected-F route.
This module proves numerical envelope estimates only, not an F-integral bound. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

 def selectedFactorialEnvelope (C : ℝ) (j n : ℕ) : ℝ :=
  C^(2*n)*((2*n:ℕ):ℝ)^j/((2:ℝ)^n*(n.factorial:ℝ))

 theorem polynomial_le_factorial_exp (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x^j ≤ (j.factorial:ℝ)*Real.exp x := by
  have hh := Real.pow_div_factorial_le_exp x hx j
  have hp : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h := (div_le_iff₀ hp).mp hh
  simpa only [mul_comm] using h

 theorem selectedFactorialEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C) (j n : ℕ) :
    0 ≤ selectedFactorialEnvelope C j n := by unfold selectedFactorialEnvelope; positivity

 theorem selectedFactorialEnvelope_le {C : ℝ} (hC : 0 ≤ C) (j n : ℕ) :
    selectedFactorialEnvelope C j n ≤
      (j.factorial:ℝ)*((C^2*Real.exp 2/2)^n/(n.factorial:ℝ)) := by
  have hpoly := polynomial_le_factorial_exp j (show 0 ≤ ((2*n:ℕ):ℝ) by positivity)
  have hnonneg : 0 ≤ C^(2*n)/((2:ℝ)^n*(n.factorial:ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hpoly hnonneg
  have hexp : Real.exp ((2*n:ℕ):ℝ) = (Real.exp 2)^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at hh
  calc
    selectedFactorialEnvelope C j n = C^(2*n)/((2:ℝ)^n*(n.factorial:ℝ))*((2*n:ℕ):ℝ)^j := by
      unfold selectedFactorialEnvelope
      ring
    _ ≤ C^(2*n)/((2:ℝ)^n*(n.factorial:ℝ))*((j.factorial:ℝ)*(Real.exp 2)^n) := hh
    _ = (j.factorial:ℝ)*((C^2*Real.exp 2/2)^n/(n.factorial:ℝ)) := by
      rw [pow_mul,div_pow,mul_pow]
      ring

 theorem selected_factorial_series_summable {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    Summable (selectedFactorialEnvelope C j) := by
  apply ((Real.summable_pow_div_factorial (C^2*Real.exp 2/2)).mul_left (j.factorial:ℝ)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (selectedFactorialEnvelope_nonneg hC j n)]
  exact selectedFactorialEnvelope_le hC j n

 theorem selected_positive_even_series_summable {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    Summable (fun n => selectedFactorialEnvelope C j (n+1)) :=
  (selected_factorial_series_summable hC j).comp_injective Nat.succ_injective

 theorem selected_factorial_window_bound {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Finset ℕ, ∑ n ∈ S, selectedFactorialEnvelope C j n ≤ B := by
  refine ⟨max 1 (∑' n, selectedFactorialEnvelope C j n),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro S
  exact (Summable.sum_le_tsum S (fun n _ => selectedFactorialEnvelope_nonneg hC j n)
    (selected_factorial_series_summable hC j)).trans (le_max_right _ _)

/-- Any prescribed exponential weight is summable; this permits arbitrary
powers of epsilon after a logarithmic particle-number cutoff. -/
theorem selected_factorial_exp_summable {C : ℝ} (hC : 0 ≤ C) (j : ℕ) (R : ℝ) :
    Summable (fun (n : ℕ) => Real.exp (R*(n:ℝ))*selectedFactorialEnvelope C j n) := by
  apply ((Real.summable_pow_div_factorial (Real.exp R*(C^2*Real.exp 2/2))).mul_left
    (j.factorial:ℝ)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (selectedFactorialEnvelope_nonneg hC j n))]
  have hh := mul_le_mul_of_nonneg_left (selectedFactorialEnvelope_le hC j n)
    (Real.exp_pos (R*(n:ℝ))).le
  have he : Real.exp (R*(n:ℝ)) = (Real.exp R)^n := by
    rw [mul_comm,Real.exp_nat_mul]
  rw [he] at hh
  rw [he,mul_pow]
  convert hh using 1; ring

theorem selected_factorial_exponential_tail {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ∀ S : Finset ℕ, (∀ n ∈ S, x ≤ (n:ℝ)) →
      ∑ n ∈ S, selectedFactorialEnvelope C j n ≤ B*Real.exp (-R*x) := by
  let f := fun (n : ℕ) => Real.exp (R*(n:ℝ))*selectedFactorialEnvelope C j n
  have hf := selected_factorial_exp_summable hC j R
  let B := max 1 (∑' n,f n)
  refine ⟨B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x S hS
  have hpoint (n : ℕ) (hn : n ∈ S) :
      selectedFactorialEnvelope C j n ≤ Real.exp (-R*x)*f n := by
    have hx : 0 ≤ R*((n:ℝ)-x) := mul_nonneg hR (sub_nonneg.mpr (hS n hn))
    have he : 1 ≤ Real.exp (-R*x)*Real.exp (R*(n:ℝ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right he (selectedFactorialEnvelope_nonneg hC j n)
    simpa only [one_mul,mul_assoc] using hh
  calc
    _ ≤ ∑ n ∈ S, Real.exp (-R*x)*f n := Finset.sum_le_sum hpoint
    _ = Real.exp (-R*x)*(∑ n ∈ S,f n) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-R*x)*B := mul_le_mul_of_nonneg_left
      ((Summable.sum_le_tsum S (fun n _ => mul_nonneg (Real.exp_pos _).le
        (selectedFactorialEnvelope_nonneg hC j n)) hf).trans (le_max_right _ _))
      (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem log_square_prefactor_eventually {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ H : ℝ in Filter.atTop, K*Real.log (1+H)^2 ≤ H := by
  have hden : 0 < 2*(K+1) := by positivity
  have hh := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show 0 < (1:ℝ)/(2*(K+1)) by positivity)
  have ht := Filter.tendsto_atTop_add_const_left Filter.atTop 1
    (Filter.tendsto_id : Filter.Tendsto (fun H : ℝ => H) Filter.atTop Filter.atTop)
  have he := ht.eventually hh
  filter_upwards [he,Filter.eventually_ge_atTop (1:ℝ)] with H hb hH
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (1+H))),id_eq,
    abs_of_nonneg (show 0 ≤ 1+H by linarith)] at hb
  have hm := (le_div_iff₀ hden).mp (show Real.log (1+H)^2 ≤ (1+H)/(2*(K+1)) by
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hb)
  nlinarith [sq_nonneg (Real.log (1+H))]

/-- Uniform finite-window tail after the logarithmic cutoff, including the
Gaussian compact-assignment prefactor. All constants precede H and the window. -/
theorem selected_factorial_logarithmic_tail {C K a Q : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (ha : 0 < a) (hQ : 0 ≤ Q) (j : ℕ) :
    ∃ B H₀ : ℝ, 0 < B ∧ ∀ H ≥ H₀, ∀ S : Finset ℕ,
      (∀ n ∈ S, a*H ≤ (n:ℝ)) →
      Real.exp (K*Real.log (1+H)^2)*
        (∑ n ∈ S,selectedFactorialEnvelope C j n) ≤ B*Real.exp (-Q*H) := by
  let R := (Q+1)/a
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨B,hB,hbound⟩ := selected_factorial_exponential_tail hC j hR
  obtain ⟨H₀,hH₀⟩ := Filter.eventually_atTop.mp (log_square_prefactor_eventually hK)
  refine ⟨B,H₀,hB,?_⟩
  intro H hH S hS
  have hb := hbound (a*H) S hS
  have he := Real.exp_le_exp.mpr (hH₀ H hH)
  have hs : 0 ≤ ∑ n ∈ S,selectedFactorialEnvelope C j n :=
    Finset.sum_nonneg (fun n _ => selectedFactorialEnvelope_nonneg hC j n)
  calc
    _ ≤ Real.exp H*(B*Real.exp (-R*(a*H))) := mul_le_mul he hb hs (Real.exp_pos H).le
    _ = B*Real.exp (-Q*H) := by
      rw [show Real.exp H*(B*Real.exp (-R*(a*H))) =
        B*(Real.exp H*Real.exp (-R*(a*H))) by ring,← Real.exp_add]
      congr 2
      dsimp [R]
      field_simp
      ring

theorem selected_factorial_logarithmic_tsum_tail {C K a Q : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (ha : 0 < a) (hQ : 0 ≤ Q) (j : ℕ) :
    ∃ B H₀ : ℝ, 0 < B ∧ ∀ H ≥ H₀,
      Real.exp (K*Real.log (1+H)^2)*
        (∑' n : ℕ, if a*H ≤ (n:ℝ) then selectedFactorialEnvelope C j n else 0)
          ≤ B*Real.exp (-Q*H) := by
  obtain ⟨B,H₀,hB,hbound⟩ := selected_factorial_logarithmic_tail hC hK ha hQ j
  refine ⟨B,H₀,hB,?_⟩
  intro H hH
  rw [← tsum_mul_left]
  apply Real.tsum_le_of_sum_le
  · intro n
    apply mul_nonneg (Real.exp_pos _).le
    split_ifs
    · exact selectedFactorialEnvelope_nonneg hC j n
    · exact le_rfl
  · intro S
    rw [← Finset.mul_sum,← Finset.sum_filter]
    exact hbound H hH (S.filter (fun n => a*H ≤ (n:ℝ)))
      (fun n hn => (Finset.mem_filter.mp hn).2)

/-- The full selected factorial tail is smaller than every prescribed
exponential in the logarithmic variable H, including its Gaussian prefactor. -/
theorem selected_factorial_tail_ratio_tendsto {C K a Q : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (ha : 0 < a) (hQ : 0 ≤ Q) (j : ℕ) :
    Filter.Tendsto (fun H : ℝ =>
      (Real.exp (K*Real.log (1+H)^2)*
        (∑' n : ℕ, if a*H ≤ (n:ℝ) then selectedFactorialEnvelope C j n else 0)) /
          Real.exp (-Q*H)) Filter.atTop (nhds 0) := by
  obtain ⟨B,H₀,hB,hbound⟩ := selected_factorial_logarithmic_tsum_tail hC hK ha
    (show 0 ≤ Q+1 by linarith) j
  refine squeeze_zero' (g := fun H => B*Real.exp (-H)) ?_ ?_ ?_
  · apply Filter.Eventually.of_forall
    intro H
    apply div_nonneg (mul_nonneg (Real.exp_pos _).le _) (Real.exp_pos _).le
    apply tsum_nonneg
    intro n
    split_ifs
    · exact selectedFactorialEnvelope_nonneg hC j n
    · exact le_rfl
  · filter_upwards [Filter.eventually_ge_atTop H₀] with H hH
    have hh := div_le_div_of_nonneg_right (hbound H hH) (Real.exp_pos (-Q*H)).le
    have he : B*Real.exp (-(Q+1)*H)/Real.exp (-Q*H) = B*Real.exp (-H) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 2
      ring
    exact hh.trans_eq he
  · simpa only [mul_zero,Function.comp_def] using
      (Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot).const_mul B

open Filter Set
open scoped Topology
 theorem selected_factorial_epsilon_tail {C K a Q : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (ha : 0 < a) (hQ : 0 ≤ Q) (j : ℕ) :
    Tendsto (fun eps : ℝ =>
      (Real.exp (K*Real.log (1-Real.log eps)^2)*
        (∑' n : ℕ, if a*(-Real.log eps) ≤ (n:ℝ)
          then selectedFactorialEnvelope C j n else 0)) / eps^Q)
      (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun eps : ℝ => -Real.log eps) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hh := (selected_factorial_tail_ratio_tendsto hC hK ha hQ j).comp ht
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hp : 0 < eps := heps
  simp only [Function.comp_def,sub_eq_add_neg]
  rw [Real.rpow_def_of_pos hp]
  congr 2
  ring

end
end IsingBulk.Tail
