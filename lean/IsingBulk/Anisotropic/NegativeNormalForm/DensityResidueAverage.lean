import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueSlope

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

 theorem inverse_near_one_bound (z : ℂ) (hz : ‖z-1‖≤1/2) :
    z≠0 ∧ ‖z⁻¹‖≤2 ∧ ‖z⁻¹-1‖≤2*‖z-1‖ := by
  have hlow : 1/2≤‖z‖ := by
    have h := norm_sub_le (z-1) z
    rw [sub_sub_cancel_left,norm_neg,norm_one] at h
    linarith
  have hzn : 0<‖z‖ := by linarith
  have hn : z≠0 := norm_pos_iff.mp hzn
  have hi : ‖z⁻¹‖≤2 := by
    rw [norm_inv]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hzn).mpr (by linarith)
  refine ⟨hn,hi,?_⟩
  rw [show z⁻¹-1=-(z-1)*z⁻¹ by field_simp; ring,norm_mul,norm_neg]
  nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg (z-1))]

 theorem average_relative_error {n : ℕ} (hn : n≠0) (f : Fin n→ℂ) :
    ‖(∑i,f i)/(n:ℂ)-1‖≤(∑i,‖f i-1‖)/(n:ℝ) := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
  have he : (∑i,f i)/(n:ℂ)-1=(∑i,(f i-1))/(n:ℂ) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    field_simp
  rw [he,norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg n)

 theorem inverse_average_relative_error {n : ℕ} (hn : n≠0) (f : Fin n→ℂ)
    (hf : ∀i,‖f i-1‖≤1/2) :
    (∑i,f i)/(n:ℂ)≠0 ∧ ‖((∑i,f i)/(n:ℂ))⁻¹‖≤2 ∧
      ‖((∑i,f i)/(n:ℂ))⁻¹-1‖≤2*((∑i,‖f i-1‖)/(n:ℝ)) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := average_relative_error hn f
  have hsum : (∑i,‖f i-1‖)≤(n:ℝ)/2 := by
    have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hf i)
    simpa [div_eq_mul_inv] using h
  have hclose : ‖(∑i,f i)/(n:ℂ)-1‖≤1/2 :=
    he.trans ((div_le_iff₀ hnR).mpr (by linarith))
  obtain ⟨hne,hb,he'⟩ := inverse_near_one_bound _ hclose
  exact ⟨hne,hb,he'.trans (mul_le_mul_of_nonneg_left he (by norm_num))⟩

/-- Exact inverse normalized Γ_t, with nonvanishing established by the actual
finite average and its scalar bounds. -/
theorem poleParameterDerivative_inverse_ratio {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (hc : centralParameterSlope B phi d≠0)
    (ha : ∀i,AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i))
    (hf : ∀i,‖residueSlopeRatio B phi hphi (t,(d,v i))-1‖≤1/2) :
    poleParameterDerivative B phi hphi d t v≠0 ∧
    ‖((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v‖≤2 ∧
    ‖((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v-1‖≤
      2*((∑i,‖residueSlopeRatio B phi hphi (t,(d,v i))-1‖)/(n:ℝ)) := by
  let f : Fin n→ℂ := fun i => residueSlopeRatio B phi hphi (t,(d,v i))
  obtain ⟨hne,hbound,herr⟩ := inverse_average_relative_error hn f hf
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
  have hs : (∑i,f i)≠0 := by intro h; exact hne (by rw [h,zero_div])
  have hg : poleParameterDerivative B phi hphi d t v=centralParameterSlope B phi d*(∑i,f i) := by
    rw [poleParameterDerivative_eq_sum B phi hphi d t v ha,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f,residueSlopeRatio]
    field_simp
  have hid : ((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v=
      ((∑i,f i)/(n:ℂ))⁻¹ := by
    rw [hg]
    field_simp
  exact ⟨by rw [hg]; exact mul_ne_zero hc hs,by simpa [hid] using hbound,by simpa [hid] using herr⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
