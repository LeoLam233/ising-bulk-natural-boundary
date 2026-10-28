import IsingBulk.HT22.Tail.SourceCollision
import IsingBulk.HT22.Tail.ActualVandermondeScale

/-! Polynomial fixed-order costs fit inside the true N² exponential without
changing the N(N−1) collision degree or the transport loss. -/
namespace IsingBulk.HT22.Near
noncomputable section

theorem nat_cast_le_two_pow (N : ℕ) : (N:ℝ)≤2^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Nat.cast_succ,pow_succ]
    have hp : (1:ℝ)≤2^N := one_le_pow₀ (by norm_num)
    linarith

theorem polynomial_le_quadratic_exponential (N L : ℕ) :
    (N:ℝ)^L≤((2:ℝ)^L)^(N^2) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg N) (nat_cast_le_two_pow N) L
  have hNN : N≤N^2 := by nlinarith
  calc
    _ ≤ (2^N)^L := hpow
    _ = ((2:ℝ)^L)^N := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hNN

theorem constant_le_quadratic_pow {A : ℝ} (hA : 1≤A) {N : ℕ} (hN : 0<N) :
    A≤A^(N^2) := by
  have hNN : 1≤N^2 := by nlinarith
  simpa only [pow_one] using pow_le_pow_right₀ hA hNN

theorem quadratic_prefactor_absorption {A B C V : ℝ}
    (_hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hV : 0≤V) (L : ℕ) :
    ∃ K : ℝ, 1≤K ∧ ∀ N : ℕ, 0<N →
      A*B^N*C^(N^2)*(N:ℝ)^L*V^(N*(N-1))≤K^(N^2) := by
  let a := max 1 A
  let b := max 1 B
  let c := max 1 C
  let v := max 1 V
  have ha : 1≤a := le_max_left _ _
  have hb : 1≤b := le_max_left _ _
  have hc : 1≤c := le_max_left _ _
  have hv : 1≤v := le_max_left _ _
  refine ⟨a*b*c*2^L*v,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc)
        (one_le_pow₀ (by norm_num))) hv
  intro N hN
  have hNN : N≤N^2 := by nlinarith
  have hpair : N*(N-1)≤N^2 := by nlinarith [Nat.sub_le N 1]
  have haN : A≤a^(N^2) := (le_max_right _ _).trans (constant_le_quadratic_pow ha hN)
  have hbN : B^N≤b^(N^2) :=
    (pow_le_pow_left₀ hB (le_max_right _ _) _).trans (pow_le_pow_right₀ hb hNN)
  have hcN : C^(N^2)≤c^(N^2) := pow_le_pow_left₀ hC (le_max_right _ _) _
  have hvN : V^(N*(N-1))≤v^(N^2) :=
    (pow_le_pow_left₀ hV (le_max_right _ _) _).trans (pow_le_pow_right₀ hv hpair)
  calc
    _ ≤ a^(N^2)*b^(N^2)*c^(N^2)*(2^L)^(N^2)*v^(N^2) := by
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul haN hbN (by positivity) (by positivity)
          · exact hcN
          · positivity
          · positivity
        · exact polynomial_le_quadratic_exponential N L
        · positivity
        · positivity
      · exact hvN
      · positivity
      · positivity
    _ = _ := by simp only [mul_pow]

end
end IsingBulk.HT22.Near
