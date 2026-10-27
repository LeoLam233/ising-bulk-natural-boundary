import IsingBulk.Preferred22.AbsoluteTail

/-! Exact conversion of the proved j=0 determinant/coarea factors to the
manuscript's q28 powers, uniformly over every positive diameter. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem zeroth_shell_factorization (n : ℕ) (A C D H : ℝ) {r T : ℝ}
    (hr : 0<r) (hT : 0<T) :
    2*(D/Real.sqrt (n+2:ℕ))^(n+2)*(r/Real.sqrt T)^(n+2)*
      (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n) =
    (2*C*(32*A)^n*shellOrderEnvelope D 1 (n+2))*
      (r^(2*n+1)/(Real.sqrt T)^(2*n+1))*H := by
  have hs : Real.sqrt T≠0 := (Real.sqrt_pos.2 hT).ne'
  have hn : Real.sqrt (n+2:ℕ)≠0 := (Real.sqrt_pos.2 (by positivity : (0:ℝ)<(n+2:ℕ))).ne'
  rw [show 2*n+1=n+n+1 by omega]
  simp only [shellOrderEnvelope,pow_one,pow_add,pow_two,mul_pow,div_pow]
  field_simp

theorem zeroth_shell_geometric_powers (n : ℕ) {r T : ℝ} (_hr : 0<r) (hT : 0<T) :
    r^(2*n+1)/(Real.sqrt T)^(2*n+1) =
      r^(2*((n+2:ℕ):ℝ)-3)*T^(-((n+2:ℕ):ℝ)+3/2) := by
  have hs : (Real.sqrt T)^(2*n+1)=T^(((2*n+1:ℕ):ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hT.le]
    congr 1
    ring
  rw [hs,div_eq_mul_inv,← Real.rpow_neg hT.le]
  have he : ((2*n+1:ℕ):ℝ)=2*((n+2:ℕ):ℝ)-3 := by push_cast; ring
  rw [← Real.rpow_natCast,he]
  congr 2
  ring

theorem zeroth_shell_constant_absorption {A C D : ℝ} (hA : 0<A) (_hC : 0<C) (hD : 0<D) :
    ∃ E : ℝ,0<E ∧ ∀ n : ℕ,
      2*C*(32*A)^n*shellOrderEnvelope D 1 (n+2)≤shellOrderEnvelope E 1 (n+2) := by
  let X := max 1 (32*A)
  let Y := max 1 (2*C)
  let E := D*X*Y
  have hX : 1≤X := le_max_left _ _
  have hY : 1≤Y := le_max_left _ _
  refine ⟨E,mul_pos (mul_pos hD (lt_of_lt_of_le zero_lt_one hX))
    (lt_of_lt_of_le zero_lt_one hY),?_⟩
  intro n
  have hp : (32*A)^n≤X^(n+2) :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) n).trans
      (pow_le_pow_right₀ hX (by omega))
  have hc : 2*C≤Y^(n+2) := by
    have hh := pow_le_pow_right₀ hY (show 1≤n+2 by omega)
    exact (le_max_right _ _).trans (by simpa only [pow_one] using hh)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul hc hp (by positivity) (by positivity))
    (by unfold shellOrderEnvelope; positivity : 0≤shellOrderEnvelope D 1 (n+2))
  calc
    _ ≤ Y^(n+2)*X^(n+2)*shellOrderEnvelope D 1 (n+2) := hh
    _ = _ := by dsimp [E,shellOrderEnvelope]; simp only [pow_one,mul_pow,div_pow]; ring

/-- The exact source q28 form at j=0, after all physical integrations have
already been performed. The extra N factor is the fixed polynomial J=1. -/
theorem zeroth_shell_q28_envelope {A C D : ℝ} (hA : 0<A) (hC : 0<C) (hD : 0<D) :
    ∃ E : ℝ,0<E ∧ ∀ n : ℕ,∀ r T H : ℝ,0<r → 0<T → 0≤H →
    2*(D/Real.sqrt (n+2:ℕ))^(n+2)*(r/Real.sqrt T)^(n+2)*
      (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n) ≤
    E^(n+2)*((n+2:ℕ):ℝ)^(-((n+2:ℕ):ℝ)/2+1)*
      r^(2*((n+2:ℕ):ℝ)-3)*T^(-((n+2:ℕ):ℝ)+3/2)*H := by
  obtain ⟨E,hE,hb⟩ := zeroth_shell_constant_absorption hA hC hD
  refine ⟨E,hE,?_⟩
  intro n r T H hr hT hH
  rw [zeroth_shell_factorization n A C D H hr hT,zeroth_shell_geometric_powers n hr hT]
  have hg : 0≤r^(2*((n+2:ℕ):ℝ)-3)*T^(-((n+2:ℕ):ℝ)+3/2) :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hT.le _)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb n) hg) hH
  rw [shell_order_envelope_eq_rpow E 1 (n+2) (by omega)] at hh
  simpa only [Nat.cast_one,mul_assoc] using hh

end
end IsingBulk.Preferred22
