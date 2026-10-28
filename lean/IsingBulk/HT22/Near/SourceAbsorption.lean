import IsingBulk.HT22.Near.QuadraticAbsorption

namespace IsingBulk.HT22.Near
noncomputable section
set_option maxHeartbeats 1000000

theorem transport_polynomial_bound {D B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (k MB MC N : ℕ) (hN : 0<N) :
    D^2+2^k*(2*(N:ℝ)*(B*(N:ℝ)^MB)+2*(N:ℝ)^2*(C*(N:ℝ)^MC))≤
      (D^2+2^(k+1)*(B+C))*(N:ℝ)^(max (MB+1) (MC+2)) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have h1 : 1≤(N:ℝ)^(max (MB+1) (MC+2)) := one_le_pow₀ hn
  have hb := pow_le_pow_right₀ hn (le_max_left (MB+1) (MC+2))
  have hc := pow_le_pow_right₀ hn (le_max_right (MB+1) (MC+2))
  have hd := mul_le_mul_of_nonneg_left h1 (sq_nonneg D)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0≤2*B by positivity)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0≤2*C by positivity)
  rw [pow_succ] at hb'
  rw [pow_add] at hc'
  have hh := mul_le_mul_of_nonneg_left (add_le_add hb' hc') (show 0≤(2:ℝ)^k by positivity)
  rw [pow_succ (2:ℝ) k]
  convert add_le_add hd hh using 1 <;> ring

theorem source_near_prefactor_absorption {RA Q RB RC RV D : ℝ}
    (hRA : 0≤RA) (hQ : 0≤Q) (hRB : 0≤RB) (hRC : 0≤RC)
    (hRV : 0≤RV) (hD : 0≤D) (k L MB MC : ℕ) :
    ∃ E : ℝ, 1≤E ∧ ∀ N : ℕ, 0<N → ∀ Z : ℝ, 1≤Z →
      (((2^k*(RA^N*(N:ℝ)^L)*(2^k*((2^k*(2^k*Q*Q))^N))^N)/Z)*D^k)*
        (D^2+2^k*(2*(N:ℝ)*(RB*(N:ℝ)^MB)+2*(N:ℝ)^2*(RC*(N:ℝ)^MC)))^k*
        RV^(N*(N-1))≤E^(N^2) := by
  let P := max (MB+1) (MC+2)
  let A := (2:ℝ)^k*D^k*(D^2+2^(k+1)*(RB+RC))^k
  let B := RA*2^k
  let C := (2:ℝ)^k*(2^k*Q*Q)
  obtain ⟨E,hE,hbound⟩ := quadratic_prefactor_absorption
    (by dsimp [A];positivity : 0≤A) (by dsimp [B];positivity : 0≤B)
    (by dsimp [C];positivity : 0≤C) hRV (L+P*k)
  refine ⟨E,hE,?_⟩
  intro N hN Z hZ
  have hp := pow_le_pow_left₀
    (by positivity : 0≤D^2+2^k*(2*(N:ℝ)*(RB*(N:ℝ)^MB)+2*(N:ℝ)^2*(RC*(N:ℝ)^MC)))
    (transport_polynomial_bound hRB hRC k MB MC N hN) k
  have hden : (2^k*(RA^N*(N:ℝ)^L)*(2^k*((2^k*(2^k*Q*Q))^N))^N)/Z≤
      2^k*(RA^N*(N:ℝ)^L)*(2^k*((2^k*(2^k*Q*Q))^N))^N :=
    div_le_self (by positivity) hZ
  calc
    _ ≤ ((2^k*(RA^N*(N:ℝ)^L)*(2^k*((2^k*(2^k*Q*Q))^N))^N)*D^k)*
        ((D^2+2^(k+1)*(RB+RC))*(N:ℝ)^P)^k*RV^(N*(N-1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hden (by positivity)) hp (by positivity) (by positivity))
        (by positivity)
    _ = A*B^N*C^(N^2)*(N:ℝ)^(L+P*k)*RV^(N*(N-1)) := by
      dsimp only [A,B,C]
      simp only [mul_pow,pow_add,pow_mul,pow_two]
      ring
    _ ≤ _ := hbound N hN

theorem physical_normalizer_norm_ge_one (N : ℕ) :
    1≤‖(N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)‖ := by
  simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos N)))
    (one_le_pow₀ (by linarith [Real.one_le_pi_div_two]))

end
end IsingBulk.HT22.Near
