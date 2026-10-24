import IsingBulk.Anisotropic.NegativeDominance.GaussianErrorSum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

def gaussianEnvelope (a C : ℝ) (N j : ℕ) : ℝ :=
  Real.exp (-a*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+C*((j : ℝ)+1))

theorem gaussianEnvelope_mono {a b C D : ℝ} (hba : b≤a) (hCD : C≤D) (N j : ℕ) :
    gaussianEnvelope a C N j≤gaussianEnvelope b D N j := by
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right hba (sq_nonneg (N : ℝ))
  have h2 := mul_le_mul_of_nonneg_right hCD (show 0≤(j : ℝ)+1 by positivity)
  linarith

theorem gaussianEnvelope_add (a b C D : ℝ) (N j : ℕ) :
    gaussianEnvelope a C N j+gaussianEnvelope b D N j≤
      gaussianEnvelope (min a b) (max C D+Real.log 2) N j := by
  have h1 := gaussianEnvelope_mono (min_le_left a b) (le_max_left C D) N j
  have h2 := gaussianEnvelope_mono (min_le_right a b) (le_max_right C D) N j
  have he : 2*gaussianEnvelope (min a b) (max C D) N j≤
      gaussianEnvelope (min a b) (max C D+Real.log 2) N j := by
    rw [gaussianEnvelope,gaussianEnvelope,show (2 : ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    have hh : 0≤Real.log 2*(j : ℝ) := mul_nonneg (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg j)
    nlinarith only [hh]
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
