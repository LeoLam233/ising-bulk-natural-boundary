import IsingBulk.Anisotropic.NegativeDominance.TauLogarithm

/-! Uniform first differences of the actual negative-edge distances. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem log_increment_bounds (x d : ℝ) (hx : 0 < x) (hd : 0 ≤ d) :
    d/(x+d) ≤ Real.log (x+d)-Real.log x ∧
      Real.log (x+d)-Real.log x ≤ d/x := by
  have hxd : 0 < x+d := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (x+d)/x by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < x/(x+d) by positivity)
  rw [Real.log_div hxd.ne' hx.ne'] at h1
  rw [Real.log_div hx.ne' hxd.ne'] at h2
  have he1 : (x+d)/x-1=d/x := by field_simp; ring
  have he2 : x/(x+d)-1= -d/(x+d) := by field_simp; ring
  rw [he1] at h1
  rw [he2] at h2
  rw [neg_div] at h2
  exact ⟨by linarith, h1⟩

theorem log_tau_step_bounds (n d : ℕ) (hn : 2 ≤ n) :
    2*(d : ℝ)/((n : ℝ)+d)-Real.pi^2/(10*(n : ℝ)^2) ≤
      Real.log (tau n)-Real.log (tau (n+d)) ∧
    Real.log (tau n)-Real.log (tau (n+d)) ≤
      2*(d : ℝ)/(n : ℝ)+Real.pi^2/(10*((n : ℝ)+d)^2) := by
  obtain ⟨hl, hu⟩ := log_increment_bounds n d (by positivity) (by positivity)
  obtain ⟨hnl, hnu⟩ := log_tau_error_bounds n hn
  obtain ⟨hdl, hdu⟩ := log_tau_error_bounds (n+d) (by omega)
  push_cast at hdl hdu
  simp only [mul_div_assoc]
  constructor <;> linarith

theorem log_tau_step_comparable (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hdn : d ≤ n) (hpi : Real.pi^2 ≤ (n : ℝ)) :
    (d : ℝ)/(2*(n : ℝ)) ≤ Real.log (tau n)-Real.log (tau (n+d)) ∧
      Real.log (tau n)-Real.log (tau (n+d)) ≤ 3*(d : ℝ)/(n : ℝ) := by
  obtain ⟨hl, hu⟩ := log_tau_step_bounds n d hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hlow : (d : ℝ)/(n : ℝ) ≤ 2*(d : ℝ)/((n : ℝ)+d) := by
    apply (div_le_div_iff₀ hn0 (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hdn' (show (0 : ℝ) ≤ d by positivity)]
  have herr : Real.pi^2/(10*(n : ℝ)^2) ≤ (d : ℝ)/(2*(n : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h1 := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 2*(n : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ (n : ℝ)^2 by positivity)
    nlinarith
  have herr' : Real.pi^2/(10*((n : ℝ)+d)^2) ≤ Real.pi^2/(10*(n : ℝ)^2) := by
    gcongr
    linarith [show (0 : ℝ) ≤ d by positivity]
  have he : (d : ℝ)/(2*(n : ℝ)) = ((d : ℝ)/(n : ℝ))/2 := by ring
  rw [he] at herr ⊢
  simp only [mul_div_assoc] at hl hu hlow ⊢
  constructor <;> linarith

end
end IsingBulk.Anisotropic.NegativeDominance
