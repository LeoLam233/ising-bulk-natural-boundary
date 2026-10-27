import IsingBulk.Preferred22.RootMovement

/-! Quantitative preservation of the actual one-body denominator under
relative perturbation of its physical center root. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1100000

theorem preferred_oneBody_relative_movement {W w : ℂ} (hW : OffRealSegment W)
    {D η : ℝ} (hD : 0<D) (hgap : D≤‖W^2-1‖)
    (hη : 0≤η) (hη1 : η≤1) (hsmall : 3*η≤Real.sqrt D)
    (hrel : ‖w/physicalRoot W-1‖≤η) :
    1-w^2≠0 ∧ ‖oneBody w‖≤4*‖oneBody (physicalRoot W)‖ := by
  let z := physicalRoot W
  have hz : z≠0 := physicalRoot_ne_zero W
  have hz0 : 0<‖z‖ := norm_pos_iff.mpr hz
  have hz1 : ‖z‖≤1 := (physicalRoot_inside hW).le
  have hdiff : ‖W-z‖^2=‖W^2-1‖ := by
    rw [←norm_pow]
    congr 1
    have h := physicalRoot_discriminant W
    dsimp only [z]
    linear_combination h
  have hsD : Real.sqrt D≤‖W-z‖ := by
    have hs := Real.sq_sqrt hD.le
    have hn := norm_nonneg (W-z)
    have hp := Real.sqrt_nonneg D
    nlinarith
  have he : 1-z^2=2*z*(W-z) := by
    have h := physicalRoot_quadratic W
    dsimp only [z]
    linear_combination h
  have hden : 2*‖z‖*Real.sqrt D≤‖1-z^2‖ := by
    rw [he,norm_mul,norm_mul,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hsD (by positivity)
  have hdenpos : 0<‖1-z^2‖ := (by positivity : 0<2*‖z‖*Real.sqrt D).trans_le hden
  have hwm : ‖w-z‖≤η*‖z‖ := by
    have hew : w-z=(w/z-1)*z := by field_simp
    rw [hew,norm_mul]
    exact mul_le_mul_of_nonneg_right hrel (norm_nonneg _)
  have hwn : ‖w‖≤2*‖z‖ := by
    have hn := norm_sub_norm_le w z
    nlinarith [mul_le_mul_of_nonneg_right hη1 (norm_nonneg z)]
  have hsum : ‖w+z‖≤3 := by
    have hn := norm_add_le w z
    linarith
  have hsq : ‖w^2-z^2‖≤3*η*‖z‖ := by
    rw [show w^2-z^2=(w-z)*(w+z) by ring,norm_mul]
    have h := mul_le_mul hwm hsum (norm_nonneg _) (mul_nonneg hη (norm_nonneg _))
    nlinarith
  have hsqhalf : ‖w^2-z^2‖≤‖1-z^2‖/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)
    nlinarith
  have hnew : ‖1-z^2‖/2≤‖1-w^2‖ := by
    have hn := norm_sub_norm_le (1-z^2) (1-w^2)
    rw [show (1-z^2)-(1-w^2)=w^2-z^2 by ring] at hn
    linarith
  have hnewpos : 0<‖1-w^2‖ := (by positivity : 0<‖1-z^2‖/2).trans_le hnew
  refine ⟨norm_pos_iff.mp hnewpos,?_⟩
  simp only [oneBody,norm_div,norm_mul,Complex.norm_ofNat]
  calc
    2*‖w‖/‖1-w^2‖ ≤ (4*‖z‖)/(‖1-z^2‖/2) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hnew
    _ = 4*(2*‖z‖/‖1-z^2‖) := by ring

end
end IsingBulk.Preferred22
