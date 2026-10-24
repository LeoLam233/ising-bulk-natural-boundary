import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section

/-- The factorial loss in the two-Pfaffian Hadamard estimate is genuinely
summable. This elementary estimate avoids an asymptotic Stirling premise. -/
theorem half_power_factorial_bound (N : ℕ) :
    (N:ℝ)^(N-N/2)/(N.factorial:ℝ) ≤
      (2:ℝ)^(N-N/2)/((N/2).factorial:ℝ) := by
  let n := N/2
  let k := N-n
  have hnk : n+k=N := Nat.add_sub_of_le (Nat.div_le_self N 2)
  have hf : (n.factorial:ℝ)*(n+1:ℝ)^k ≤ (N.factorial:ℝ) := by
    exact_mod_cast (hnk ▸ (Nat.factorial_mul_pow_le_factorial (m := n) (n := k)))
  have hN : (N:ℝ) ≤ 2*(n+1:ℝ) := by
    have hn : N ≤ 2*(n+1) := by dsimp [n]; omega
    exact_mod_cast hn
  have hp : (N:ℝ)^k ≤ 2^k*(n+1:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hN _
  have hnpos : 0 < (n.factorial:ℝ) := by positivity
  have hNpos : 0 < (N.factorial:ℝ) := by positivity
  apply (div_le_div_iff₀ hNpos hnpos).mpr
  exact (mul_le_mul_of_nonneg_right hp hnpos.le).trans (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k])

def hadamardEnvelope (C : ℝ) (N : ℕ) : ℝ :=
  C^N*(N:ℝ)^(N-N/2)/(N.factorial:ℝ)

theorem hadamardEnvelope_even_le {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    hadamardEnvelope C (2*n) ≤ (2*C^2)^n/(n.factorial:ℝ) := by
  have h := mul_le_mul_of_nonneg_left (half_power_factorial_bound (2*n)) (pow_nonneg hC (2*n))
  have hd : (2*n)/2=n := by omega
  have hs : 2*n-n=n := by omega
  simp only [hd,hs] at h
  calc
    hadamardEnvelope C (2*n) ≤ C^(2*n)*(2^n/(n.factorial:ℝ)) := by
      simpa only [hadamardEnvelope,hd,hs,mul_div_assoc] using h
    _ = _ := by rw [pow_mul,mul_pow]; ring

theorem hadamardEnvelope_odd_le {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    hadamardEnvelope C (2*n+1) ≤ 2*C*((2*C^2)^n/(n.factorial:ℝ)) := by
  have h := mul_le_mul_of_nonneg_left (half_power_factorial_bound (2*n+1)) (pow_nonneg hC (2*n+1))
  have hd : (2*n+1)/2=n := by omega
  have hs : 2*n+1-n=n+1 := by omega
  simp only [hd,hs] at h
  calc
    hadamardEnvelope C (2*n+1) ≤ C^(2*n+1)*(2^(n+1)/(n.factorial:ℝ)) := by
      simpa only [hadamardEnvelope,hd,hs,mul_div_assoc] using h
    _ = _ := by rw [pow_succ,pow_succ,pow_mul,mul_pow]; ring
theorem hadamardEnvelope_even_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun n => hadamardEnvelope C (2*n)) :=
  (Real.summable_pow_div_factorial (2*C^2)).of_nonneg_of_le
    (fun n => by unfold hadamardEnvelope; positivity) (hadamardEnvelope_even_le hC)

theorem hadamardEnvelope_odd_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun n => hadamardEnvelope C (2*n+1)) :=
  ((Real.summable_pow_div_factorial (2*C^2)).mul_left (2*C)).of_nonneg_of_le
    (fun n => by unfold hadamardEnvelope; positivity) (hadamardEnvelope_odd_le hC)

end
end IsingBulk.Anisotropic.FormFactors
