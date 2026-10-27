import IsingBulk.Preferred22.ZerothShellPowers

/-! The exact general q28 powers follow from the already integrated true
coarea factors and the h+ell=2j marked-word scale. -/
namespace IsingBulk.Preferred22
noncomputable section

/-- All transport orders retain the source q28 exponents. The prefactor
constant precedes N and every positive diameter; no shell bound is assumed. -/
theorem transported_shell_q28_envelope {A C D : ℝ} (hA : 0<A) (hC : 0<C) (hD : 0<D)
    (J j : ℕ) :
    ∃ E : ℝ,0<E ∧ ∀ n : ℕ,∀ r T H : ℝ,0<r → 0<T → 0≤H →
    (2*shellOrderEnvelope D J (n+2)*(r^(n+2)/(r^(2*j)*(Real.sqrt T)^(n+2))))*
      (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n) ≤
    E^(n+2)*((n+2:ℕ):ℝ)^(-((n+2:ℕ):ℝ)/2+((J+1:ℕ):ℝ))*
      r^(2*((n+2:ℕ):ℝ)-2*(j:ℝ)-3)*T^(-((n+2:ℕ):ℝ)+3/2)*H := by
  obtain ⟨E,hE,hb⟩ := zeroth_shell_q28_envelope hA hC hD
  refine ⟨E,hE,?_⟩
  intro n r T H hr hT hH
  have hN : (0:ℝ)<(n+2:ℕ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right (hb n r T H hr hT hH)
    (by positivity : 0≤((n+2:ℕ):ℝ)^J/r^(2*j))
  have hNp : ((n+2:ℕ):ℝ)^(-((n+2:ℕ):ℝ)/2+1)*((n+2:ℕ):ℝ)^J=
      ((n+2:ℕ):ℝ)^(-((n+2:ℕ):ℝ)/2+((J+1:ℕ):ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have hrp : r^(2*((n+2:ℕ):ℝ)-3)/r^(2*j)=r^(2*((n+2:ℕ):ℝ)-2*(j:ℝ)-3) := by
    rw [← Real.rpow_natCast,← Real.rpow_sub hr]
    congr 1
    push_cast
    ring
  calc
    _ = (2*(D/Real.sqrt (n+2:ℕ))^(n+2)*(r/Real.sqrt T)^(n+2)*
      (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n))*
        (((n+2:ℕ):ℝ)^J/r^(2*j)) := by
      unfold shellOrderEnvelope
      simp only [div_pow,mul_pow]
      ring
    _ ≤ _ := hmul
    _ = E^(n+2)*
        (((n+2:ℕ):ℝ)^(-((n+2:ℕ):ℝ)/2+1)*((n+2:ℕ):ℝ)^J)*
        (r^(2*((n+2:ℕ):ℝ)-3)/r^(2*j))*T^(-((n+2:ℕ):ℝ)+3/2)*H := by ring
    _ = _ := by rw [hNp,hrp]

end
end IsingBulk.Preferred22
