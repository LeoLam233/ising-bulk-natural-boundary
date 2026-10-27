import IsingBulk.Preferred22.NormalConvergence

/-! The exact factorial and N^(-3) Cauchy scale combine into the
manuscript's N^(3j+1) (C_j/sqrt N)^N selected-sector estimate. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1000000

theorem preferred_selected_factorial_cauchy_estimate {A H D c τ : ℝ}
    (hA : 0<A) (hH : 0<H) (hD : 0<D) (hc : 0<c) (hτ : 0<τ) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N →
      ((j.factorial:ℝ)*((H*(N:ℝ)/τ)*(Real.sqrt N*A)^N/(N.factorial:ℝ)) /
        (c*τ^2/(N:ℝ)^3)^j)*D^N ≤ C*(N:ℝ)^(3*j+1)*(C/Real.sqrt N)^N := by
  let B := Real.exp 1*A*D
  let Q := (j.factorial:ℝ)*H/(τ*(c*τ^2)^j)
  let C := max B Q
  have hB : 0<B := by dsimp only [B]; positivity
  have hQ : 0<Q := by dsimp only [Q]; positivity
  have hC : 0<C := hB.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hfact : 0<(N.factorial:ℝ) := by positivity
  have hR : 0<c*τ^2/(N:ℝ)^3 := by positivity
  have henv := sqrt_factorial_envelope hN hA.le
  have he :
      ((j.factorial:ℝ)*((H*(N:ℝ)/τ)*(Real.sqrt N*A)^N/(N.factorial:ℝ)) /
        (c*τ^2/(N:ℝ)^3)^j)*D^N =
      ((j.factorial:ℝ)*(H*(N:ℝ)/τ)/(c*τ^2/(N:ℝ)^3)^j)*
        ((Real.sqrt N*A)^N/(N.factorial:ℝ))*D^N := by ring
  rw [he]
  calc
    _ ≤ ((j.factorial:ℝ)*(H*(N:ℝ)/τ)/(c*τ^2/(N:ℝ)^3)^j)*
        (Real.exp 1*A/Real.sqrt N)^N*D^N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left henv (by positivity)) (by positivity)
    _ = Q*(N:ℝ)^(3*j+1)*(B/Real.sqrt N)^N := by
      dsimp only [Q,B]
      have hNj : (N:ℝ)^(3*j+1)=((N:ℝ)^3)^j*(N:ℝ) := by rw [pow_succ,pow_mul]
      rw [hNj]
      simp only [div_pow,mul_pow]
      field_simp
    _ ≤ C*(N:ℝ)^(3*j+1)*(C/Real.sqrt N)^N := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      · exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (le_max_left _ _) hsqrt.le) _
      · positivity
      · positivity

end
end IsingBulk.Preferred22
