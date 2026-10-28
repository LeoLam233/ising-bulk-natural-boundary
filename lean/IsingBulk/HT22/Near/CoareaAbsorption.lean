import IsingBulk.HT22.Near.QuadraticAbsorption
import IsingBulk.HT22.Tail.ShellScale

namespace IsingBulk.HT22.Near
noncomputable section

theorem coarea_quadratic_absorption {A C D : ℝ} (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) :
    ∃ E : ℝ, 1≤E ∧ ∀ n j : ℕ, ∀ Δ : ℝ, 0<Δ →
      (A^((n+3)^2)*Δ^((n+3)*(n+2))/Δ^(2*j))*C*(n+3:ℕ)*D^(n+1)*Δ^n ≤
        E^((n+3)^2)*Δ^(((n+3:ℕ):ℝ)^2-2*(j:ℝ)-3) := by
  obtain ⟨E,hE,hbound⟩ := quadratic_prefactor_absorption hC
    (show 0≤max 1 D by positivity) hA (by norm_num : (0:ℝ)≤1) 1
  refine ⟨E,hE,?_⟩
  intro n j Δ hΔ
  have hpow : D^(n+1)≤(max 1 D)^(n+3) :=
    (pow_le_pow_left₀ hD (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hcoeff : A^((n+3)^2)*C*(n+3:ℕ)*D^(n+1)≤E^((n+3)^2) := by
    have h := hbound (n+3) (by omega)
    simp only [pow_one,one_pow,mul_one] at h
    calc
      _ ≤ A^((n+3)^2)*C*(n+3:ℕ)*(max 1 D)^(n+3) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := by simpa only [mul_comm,mul_left_comm,mul_assoc] using h
  have hscale := full_product_coarea_scale_identity n j hΔ
  have hh := mul_le_mul_of_nonneg_right hcoeff
    (show 0≤(Δ^((n+3)*(n+2))/Δ^(2*j))*Δ^n by positivity)
  rw [hscale] at hh
  apply le_trans _ hh
  rw [←hscale]
  ring_nf
  exact le_refl _

end
end IsingBulk.HT22.Near
