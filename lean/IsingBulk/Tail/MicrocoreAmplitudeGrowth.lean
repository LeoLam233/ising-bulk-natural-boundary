import IsingBulk.Tail.MicrocoreAmplitudeBound

/-! Explicit exp(O_J(N²)) conversion of the proved actual amplitude-jet
product budget. The exponent constant is fixed before all N. -/
namespace IsingBulk.Tail
noncomputable section

def microAmplitudeBudget (J : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  2^J*(2^J*((2^J*C)^N+(2^J*C)^N)*(2^J*(2^J*C)^N)^N)*(2^J*C)^N

 theorem microAmplitudeBudget_exp (J : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      microAmplitudeBudget J C N ≤ Real.exp (A*(N:ℝ)^2) := by
  let a : ℝ := 2^J
  let B := a*C
  let D := 2*B
  have ha : 1 ≤ a := one_le_pow₀ (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have hBD : B ≤ D := by dsimp [D]; linarith
  have haD : a ≤ D := by dsimp [B,D] at *; nlinarith
  have hDp : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos (by linarith)
  refine ⟨7*Real.log D,by positivity,?_⟩
  intro N hN
  have hpN : B^N ≤ D^N := pow_le_pow_left₀ (by linarith) hBD N
  have hsum : B^N+B^N ≤ D^(N+1) := by
    rw [pow_succ]
    have hpos : 0 ≤ D^N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD hpos]
  have hprod : (a*B^N)^N ≤ D^((N+1)*N) := by
    have hh : a*B^N ≤ D^(N+1) := by
      rw [pow_succ']
      exact mul_le_mul haD hpN (by positivity) (by positivity)
    have hh' := pow_le_pow_left₀ (show 0 ≤ a*B^N by positivity) hh N
    simpa only [pow_mul] using hh'
  have hbudget : microAmplitudeBudget J C N ≤ D^(N^2+3*N+3) := by
    change a*(a*(B^N+B^N)*(a*B^N)^N)*B^N ≤ _
    calc
      _ ≤ D*(D*D^(N+1)*D^((N+1)*N))*D^N := by gcongr
      _ = _ := by
        simp only [← pow_succ',← pow_add]
        congr 1
        ring
  have hexponent : N^2+3*N+3 ≤ 7*N^2 := by nlinarith
  calc
    _ ≤ D^(N^2+3*N+3) := hbudget
    _ ≤ D^(7*N^2) := pow_le_pow_right₀ (by linarith) hexponent
    _ = Real.exp ((7*Real.log D)*(N:ℝ)^2) := by
      conv_lhs => rw [← Real.exp_log hDp]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Source amplitude jets with constants and neighborhood fixed before N.
The full Vandermonde square is not divided out after differentiation. -/
 theorem micro_amplitude_uniform_exponential_jets (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) (J : ℕ) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ N : ℕ, 1 ≤ N → ∀ s : ℂ, ∀ φ : Fin N → ℂ,
      ‖s-s₀‖ < r → (∀ i, ‖φ i‖ < r) → ∀ j ≤ J,
      ‖iteratedFDeriv ℂ j (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2) (s,φ)‖ ≤
        Real.exp (A*(N:ℝ)^2) := by
  obtain ⟨C,r,hC,hr,hf⟩ := micro_factor_bounds_uniform s₀ c hs hS hc J
  obtain ⟨A,hA,hbudget⟩ := microAmplitudeBudget_exp J C hC
  refine ⟨A,r,hA,hr,?_⟩
  intro N hN s φ hs' hφ j hj
  have hh := micro_amplitude_jet_product_budget (s,φ) J C hC (hf N s φ hs' hφ)
  exact (hh.bound j hj).trans (hbudget N hN)

end
end IsingBulk.Tail
