import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedEnergyControl

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem absoluteEnergy_le_card_mul_norm_sq {n : ℕ} (v : Config n) :
    absoluteEnergy v≤(n:ℝ)*‖v‖^2 := by
  calc
    _ ≤ ∑ _i : Fin n, ‖v‖^2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = _ := by simp

theorem absoluteEnergy_smul_complex {n : ℕ} (c : ℂ) (v : Config n) :
    absoluteEnergy (c • v)=‖c‖^2*absoluteEnergy v := by
  simp only [absoluteEnergy,Pi.smul_apply,norm_smul,mul_pow,Finset.mul_sum]

theorem absoluteEnergy_sub_comm {n : ℕ} (v w : Config n) :
    absoluteEnergy (v-w)=absoluteEnergy (w-v) := by
  simp only [absoluteEnergy,Pi.sub_apply,norm_sub_rev]

theorem norm_pairing_sq_le {n : ℕ} (v w : Config n) :
    ‖pairing v w‖^2≤absoluteEnergy v*absoluteEnergy w := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_pairing_le v w) 2
  simpa only [mul_pow,Real.sq_sqrt (absoluteEnergy_nonneg v),Real.sq_sqrt (absoluteEnergy_nonneg w)] using hh

theorem meanCorrection_absoluteEnergy_error {n : ℕ} (ell w : Config n) :
    absoluteEnergy (meanCorrection ell w-w)≤absoluteEnergy w*((n:ℝ)*absoluteEnergy ell)^2 := by
  have he : meanCorrection ell w-w=(rankOneCoefficient ell*pairing w ell) • ell := by
    ext i
    simp only [meanCorrection,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,absoluteEnergy_smul_complex,norm_mul,mul_pow]
  have hq := absoluteEnergy_nonneg ell
  have hw := absoluteEnergy_nonneg w
  calc
    _ ≤ (n:ℝ)^2*(absoluteEnergy w*absoluteEnergy ell)*absoluteEnergy ell := by
      apply mul_le_mul_of_nonneg_right _ hq
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (rankOneCoefficient_norm_le ell) 2)
        (norm_pairing_sq_le w ell) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

theorem meanCorrection_energy_small {n : ℕ} (ell w : Config n)
    (hell : ‖(n:ℂ) • ell‖≤1/8) :
    absoluteEnergy (meanCorrection ell w-w)≤absoluteEnergy w/4096 := by
  have he : (n:ℝ)*‖ell‖≤1/8 := by simpa only [norm_smul,Complex.norm_natCast] using hell
  have hq : (n:ℝ)*absoluteEnergy ell≤1/64 := by
    have hh := mul_le_mul_of_nonneg_left (absoluteEnergy_le_card_mul_norm_sq ell) (Nat.cast_nonneg n : (0:ℝ)≤n)
    have hs : ((n:ℝ)*‖ell‖)^2≤(1/8:ℝ)^2 := pow_le_pow_left₀ (by positivity) he 2
    nlinarith
  have hs : ((n:ℝ)*absoluteEnergy ell)^2≤(1/64:ℝ)^2 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) (absoluteEnergy_nonneg ell)) hq 2
  exact (meanCorrection_absoluteEnergy_error ell w).trans
    ((mul_le_mul_of_nonneg_left hs (absoluteEnergy_nonneg w)).trans_eq (by ring))

theorem corrected_inverse_energy_control {n : ℕ} (hn : n≠0) (S v w y ell : Config n)
    (hv : ZeroMean v) (hP : project (fun i => v i*S i)=w)
    (hS : ∀ i, ‖S i-1‖≤1/64) (hy : meanCorrection ell w=y)
    (hell : ‖(n:ℂ) • ell‖≤1/8) :
    absoluteEnergy w≤4*absoluteEnergy y ∧ absoluteEnergy (v-y)≤absoluteEnergy y/64 := by
  have hp := projected_inverse_energy_control hn S v w (1/64) (by norm_num) (by norm_num) hv hP hS
  have hc := meanCorrection_energy_small ell w hell
  rw [hy,absoluteEnergy_sub_comm y w] at hc
  have ha := absoluteEnergy_add_le y (w-y)
  rw [add_sub_cancel] at ha
  have hw : absoluteEnergy w≤4*absoluteEnergy y := by linarith [absoluteEnergy_nonneg w]
  refine ⟨hw,?_⟩
  have hh := absoluteEnergy_add_le (v-w) (w-y)
  rw [sub_add_sub_cancel] at hh
  linarith [hp.1,hp.2,absoluteEnergy_nonneg y]

end
end IsingBulk.Anisotropic.NegativeNormalForm
