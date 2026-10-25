import IsingBulk.Joint.PhysicalField.RealFamily
import IsingBulk.Anisotropic.Final.FieldDerivative

/-! Identification of the actual independent-coupling full-site sums with
one common real physical family, and the energy-field derivative on every
positive finite anisotropy ray. -/
namespace IsingBulk.Joint.PhysicalField
noncomputable section
open Set

variable {corrH corrL : CorrelationFamily}

theorem high_physical_identification_on_ray
    (hphys : PublishedRealSpinFamily corrH corrL) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct (realSlice lam x) < 1) :
    Summable (corrH (realSlice lam x)) ∧
    FormFactors.highNormalizedBulk (complexify (realSlice lam x)) =
      (highCovarianceSum corrH (realSlice lam x):ℂ) := by
  have hs := (Anisotropic.realPhysicalIdentification_of_published 1 hlam (hphys lam hlam)).high x hx hp
  refine ⟨hs.1,?_⟩
  rw [complexify_realSlice,FormFactors.highNormalizedBulk_ratioSlice hlam
    (Anisotropic.real_mem_omegaH_of_nonneg_lt_critical hlam hx.le
      (Anisotropic.lt_criticalPoint_of_product_lt_one hlam hx.le hp))]
  exact hs.2.1

theorem low_physical_identification_on_ray
    (hphys : PublishedRealSpinFamily corrH corrL) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : 1 < realProduct (realSlice lam x)) :
    Summable (fun v => corrL (realSlice lam x) v-magnetizationSq (realSlice lam x)) ∧
    FormFactors.lowNormalizedBulk (complexify (realSlice lam x)) =
      (lowCovarianceSum corrL (realSlice lam x):ℂ) := by
  have hs := (Anisotropic.realPhysicalIdentification_of_published 1 hlam (hphys lam hlam)).low x hx hp
  refine ⟨hs.1,?_⟩
  rw [complexify_realSlice,FormFactors.lowNormalizedBulk_ratioSlice hlam
    ((Anisotropic.real_mem_omegaL_iff_product_gt_one hlam hx.le).mpr hp)]
  simpa only [lowCovarianceSum,Anisotropic.FormFactors.lowCovarianceSum,
    magnetizationSq_realSlice] using hs.2.1

/-- All independent positive real couplings, not just a fixed ratio. -/
theorem high_physical_identification (hphys : PublishedRealSpinFamily corrH corrL)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hp : realProduct (x,y) < 1) :
    Summable (corrH (x,y)) ∧
    FormFactors.highNormalizedBulk (complexify (x,y)) = (highCovarianceSum corrH (x,y):ℂ) := by
  have he := realSlice_ratio hx.ne' y
  simpa only [he] using high_physical_identification_on_ray hphys (div_pos hy hx) hx
    (show realProduct (realSlice (y/x) x) < 1 by rwa [he])

/-- The subtraction is the plus-phase vacuum at every lattice site, including
its onsite value, not the mean-zero symmetric mixture covariance. -/
theorem low_physical_identification (hphys : PublishedRealSpinFamily corrH corrL)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hp : 1 < realProduct (x,y)) :
    Summable (fun v => corrL (x,y) v-magnetizationSq (x,y)) ∧
    FormFactors.lowNormalizedBulk (complexify (x,y)) = (lowCovarianceSum corrL (x,y):ℂ) := by
  have he := realSlice_ratio hx.ne' y
  simpa only [he] using low_physical_identification_on_ray hphys (div_pos hy hx) hx
    (show 1 < realProduct (realSlice (y/x) x) by rwa [he])

/-- Real temperature rays only: the energy-field susceptibility is beta times
the reduced response. Spin-flip symmetry gives the ordinary HT derivative. -/
theorem high_energy_field_derivative {mH mL : MagnetizationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    (hfields : PublishedRealGibbsFamily corrH corrL mH mL)
    {J lam x : ℝ} (hJ : 0 < J) (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct (realSlice lam x) < 1) :
    HasDerivAt (mH J (lam*J) (x/(2*J)))
      ((x/(2*J))*highCovarianceSum corrH (realSlice lam x)) 0 ∧
    (x/(2*J):ℂ)*FormFactors.highNormalizedBulk (complexify (realSlice lam x)) =
      (((x/(2*J))*highCovarianceSum corrH (realSlice lam x):ℝ):ℂ) := by
  have G := hfields J lam hJ hlam
  have hr := Anisotropic.PhysicalField.field_response_of_gibbs_conditions
    (div_pos hx (mul_pos (by norm_num) hJ)).le (G.high x hx hp).some
    (high_physical_identification_on_ray hphys hlam hx hp).1
  refine ⟨Anisotropic.PhysicalField.hasDerivAt_of_odd_right_derivative
    (G.high_spin_flip x hx hp) hr,?_⟩
  rw [(high_physical_identification_on_ray hphys hlam hx hp).2]
  push_cast
  rfl

/-- The LT derivative is the right derivative of the plus phase. -/
theorem low_energy_field_derivative {mH mL : MagnetizationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    (hfields : PublishedRealGibbsFamily corrH corrL mH mL)
    {J lam x : ℝ} (hJ : 0 < J) (hlam : 0 < lam) (hx : 0 < x)
    (hp : 1 < realProduct (realSlice lam x)) :
    HasDerivWithinAt (mL J (lam*J) (x/(2*J)))
      ((x/(2*J))*lowCovarianceSum corrL (realSlice lam x)) (Ioi 0) 0 ∧
    (x/(2*J):ℂ)*FormFactors.lowNormalizedBulk (complexify (realSlice lam x)) =
      (((x/(2*J))*lowCovarianceSum corrL (realSlice lam x):ℝ):ℂ) := by
  have G := hfields J lam hJ hlam
  constructor
  · simpa only [lowCovarianceSum,magnetizationSq_realSlice] using
      Anisotropic.PhysicalField.field_response_of_gibbs_conditions
        (div_pos hx (mul_pos (by norm_num) hJ)).le (G.low x hx hp).some
        (low_physical_identification_on_ray hphys hlam hx hp).1
  · rw [(low_physical_identification_on_ray hphys hlam hx hp).2]
    push_cast
    rfl

theorem low_connected_onsite (hphys : PublishedRealSpinFamily corrH corrL)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hp : 1 < realProduct (x,y)) :
    corrL (x,y) (0,0)-magnetizationSq (x,y) = 1-magnetizationSq (x,y) := by
  have he := realSlice_ratio hx.ne' y
  have hs := (hphys (y/x) (div_pos hy hx)).low_onsite x hx
    (show Anisotropic.FormFactors.realProduct (y/x) x > 1 by
      change realProduct (realSlice (y/x) x) > 1; rwa [he])
  simpa only [he] using congrArg (fun v => v-magnetizationSq (x,y)) hs

end
end IsingBulk.Joint.PhysicalField
