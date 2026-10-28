import IsingBulk.HT22.Tail.BorderedNormalization

/-! The N+1 odd border with N! and the N^-3 Cauchy radius gives the
literal N^(3j+2) selected envelope. -/
namespace IsingBulk.HT22.Selected
noncomputable section
set_option maxHeartbeats 1000000

theorem selected_bordered_factorial_cauchy {A K H D c τ : ℝ}
    (hA : 0<A) (hK : 0<K) (hH : 0<H) (hD : 0<D) (hc : 0<c) (hτ : 0<τ) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N →
      ((j.factorial:ℝ)*((H*(N:ℝ)/τ)*A^N*(K*Real.sqrt (N+1))^(N+1)/(N.factorial:ℝ)) /
        (c*τ^2/(N:ℝ)^3)^j)*D^N ≤ C*(N:ℝ)^(3*j+2)*(C/Real.sqrt N)^N := by
  let B := 4*Real.exp 1*A*K*D
  let Q := (j.factorial:ℝ)*H*K/(τ*(c*τ^2)^j)
  let C := max B Q
  have hB : 0<B := by dsimp [B]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hC : 0<C := hB.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have henv := bordered_hadamard_factorial_envelope hN
  have he :
      ((j.factorial:ℝ)*((H*(N:ℝ)/τ)*A^N*(K*Real.sqrt (N+1))^(N+1)/(N.factorial:ℝ)) /
        (c*τ^2/(N:ℝ)^3)^j)*D^N =
      ((j.factorial:ℝ)*(H*(N:ℝ)/τ)*K/(c*τ^2/(N:ℝ)^3)^j)*
        ((Real.sqrt (N+1:ℕ))^(N+1)/(N.factorial:ℝ))*(A*K*D)^N := by
    simp only [mul_pow,pow_succ,Nat.cast_add,Nat.cast_one]
    ring
  rw [he]
  calc
    _ ≤ ((j.factorial:ℝ)*(H*(N:ℝ)/τ)*K/(c*τ^2/(N:ℝ)^3)^j)*
        ((N:ℝ)*((4*Real.exp 1)/Real.sqrt N)^N)*(A*K*D)^N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left henv (by positivity)) (by positivity)
    _ = Q*(N:ℝ)^(3*j+2)*(B/Real.sqrt N)^N := by
      dsimp only [Q,B]
      have hNj : (N:ℝ)^(3*j+2)=((N:ℝ)^3)^j*(N:ℝ)^2 := by rw [pow_add,pow_mul]
      rw [hNj]
      simp only [div_pow,mul_pow]
      field_simp
    _ ≤ C*(N:ℝ)^(3*j+2)*(C/Real.sqrt N)^N := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      · exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (le_max_left _ _) hsqrt.le) _
      · positivity
      · positivity

end
end IsingBulk.HT22.Selected
