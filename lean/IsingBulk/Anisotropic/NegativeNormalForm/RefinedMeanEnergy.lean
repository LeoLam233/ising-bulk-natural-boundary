import IsingBulk.Anisotropic.NegativeNormalForm.ScalarQuadraticControl
import IsingBulk.Anisotropic.NegativeNormalForm.HermitianProjection
import IsingBulk.Anisotropic.NegativeNormalForm.ReciprocalFieldBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem meanCoefficients_refined_energy {n : ℕ} (hn : n≠0)
    (S v : Config n) (s₀ : ℂ) (L D : ℝ) (_hL : 0≤L) (_hD : 0≤D)
    (hS : ∀ i, ‖S i-1‖≤1/4) (hs₀ : ‖s₀-1‖≤1/4)
    (hdelta : ∀ i, ‖S i-s₀‖≤L*(D+‖v‖)*‖v i‖) :
    absoluteEnergy (meanCoefficients S)≤
      64*L^2*(D+‖v‖)^2*absoluteEnergy v/(n:ℝ)^2 := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hq : 0≤absoluteEnergy v := Finset.sum_nonneg (fun i _ => sq_nonneg ‖v i‖)
  have hcoord (i : Fin n) : ‖s₀⁻¹-(S i)⁻¹‖≤4*L*(D+‖v‖)*‖v i‖ := by
    have hh := scalar_inverse_difference s₀ (S i) (hs₀.trans (by norm_num))
      ((hS i).trans (by norm_num))
    rw [norm_sub_rev s₀] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hdelta i) (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))
  have hnum : absoluteEnergy (fun i => s₀⁻¹-(S i)⁻¹)≤
      (4*L*(D+‖v‖))^2*absoluteEnergy v := by
    unfold absoluteEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      ‖s₀⁻¹-(S i)⁻¹‖^2 ≤ (4*L*(D+‖v‖)*‖v i‖)^2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ = _ := by ring
  have hden : (n:ℝ)/2≤‖∑ i, (S i)⁻¹‖ := by
    have hh := reciprocal_sum_norm_lower S (1/2) (fun i =>
      (scalar_reciprocal_error (S i) ((hS i).trans (by norm_num))).trans
        (by linarith [hS i]))
    nlinarith
  have hdsq : ((n:ℝ)/2)^2≤‖∑ i, (S i)⁻¹‖^2 :=
    pow_le_pow_left₀ (by positivity) hden 2
  calc
    _ ≤ absoluteEnergy (fun i => s₀⁻¹-(S i)⁻¹)/‖∑ i, (S i)⁻¹‖^2 :=
      meanCoefficients_energy_le hn S s₀⁻¹
    _ ≤ ((4*L*(D+‖v‖))^2*absoluteEnergy v)/‖∑ i, (S i)⁻¹‖^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ ((4*L*(D+‖v‖))^2*absoluteEnergy v)/((n:ℝ)/2)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdsq
    _ = _ := by field_simp; ring

theorem phaseRootMean_refined_energy (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ n : ℕ, n≠0 → ∀ (d t : ℂ) (v : Config n),
      ‖d‖<r → ‖t‖<r → ‖v‖<r →
      absoluteEnergy (meanCoefficients (fun i => Complex.sqrt (phaseEnergy B phi hphi d t (v i))))≤
        C*(‖d‖+‖v‖)^2*absoluteEnergy v/(n:ℝ)^2 := by
  obtain ⟨a,L,ha,hL,hcontrol⟩ := phaseRootEnergy_quadratic_control B phi hphi hB hBn
  obtain ⟨b,M,hb,_hM,hsmall,_hLip⟩ := phaseRootEnergy_uniform_small B phi hphi hB hBn (1/4) (by norm_num)
  refine ⟨min a b,64*L^2,lt_min ha hb,by positivity,?_⟩
  intro n hn d t v hd ht hv
  have hp (i : Fin n) : ‖(t,(d,v i))‖<min a b :=
    max_lt ht (max_lt hd ((norm_le_pi_norm v i).trans_lt hv))
  have hp0 : ‖(t,(d,(0:ℂ)))‖<min a b := max_lt ht (max_lt hd (by simpa using lt_min ha hb))
  apply meanCoefficients_refined_energy hn _ v
    (Complex.sqrt (phaseEnergy B phi hphi d t 0)) L ‖d‖ hL.le (norm_nonneg _)
  · intro i
    exact (hsmall _ ((hp i).trans_le (min_le_right _ _))).2
  · exact (hsmall _ (hp0.trans_le (min_le_right _ _))).2
  · intro i
    exact (hcontrol _ ((hp i).trans_le (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (norm_le_pi_norm v i)) hL.le)
        (norm_nonneg _))

end
end IsingBulk.Anisotropic.NegativeNormalForm
