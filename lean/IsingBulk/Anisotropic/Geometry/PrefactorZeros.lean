import IsingBulk.Anisotropic.Geometry.SpectralAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

private theorem corner_implies_spectral {lam : ℝ} {z : ℂ} (e f : ℝ)
    (he : e^2=1) (hf : f^2=1) (hp : spectralProduct lam z = (e:ℂ)*(f:ℂ)) :
    z ∈ spectralSet lam := by
  have hei : e ∈ Set.Icc (-1:ℝ) 1 := by constructor <;> nlinarith [sq_nonneg (e+1), sq_nonneg (e-1)]
  have hfi : f ∈ Set.Icc (-1:ℝ) 1 := by constructor <;> nlinarith [sq_nonneg (f+1), sq_nonneg (f-1)]
  have hc := spectral_corner_identity lam z (e:ℂ) (f:ℂ) (by exact_mod_cast he) (by exact_mod_cast hf)
  rw [hp, sub_self, zero_pow (by decide : 2≠0), sub_eq_zero] at hc
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hc with h | h
  · exact ⟨e,hei,f,hfi,by simpa [mul_comm] using h⟩
  · refine ⟨-e, ⟨by linarith [hei.2], by linarith [hei.1]⟩,
      -f, ⟨by linarith [hfi.2], by linarith [hfi.1]⟩, ?_⟩
    simpa [mul_comm, neg_add, add_comm] using h

/-- Every zero of either bulk prefactor lies in the actual unsquared spectral set. -/
theorem mem_spectralSet_of_product_sq_eq_one {lam : ℝ} {z : ℂ}
    (hp : spectralProduct lam z ^2=1) : z ∈ spectralSet lam := by
  rcases sq_eq_one_iff.mp hp with h | h
  · exact corner_implies_spectral 1 1 (by norm_num) (by norm_num) (by simpa using h)
  · exact corner_implies_spectral 1 (-1) (by norm_num) (by norm_num) (by simpa using h)

theorem product_sq_ne_one_of_not_mem_spectralSet {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSet lam) : spectralProduct lam z ^2 ≠ 1 :=
  fun h => hz (mem_spectralSet_of_product_sq_eq_one h)

end
end IsingBulk.Anisotropic
