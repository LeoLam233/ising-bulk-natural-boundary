import IsingBulk.Joint.PhysicalField.Identification

namespace IsingBulk.Joint
noncomputable section
open Set PhysicalField

theorem high_full_onsite {corrH corrL : CorrelationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hp : realProduct (x,y) < 1) :
    corrH (x,y) (0,0) = 1 := by
  have he := realSlice_ratio hx.ne' y
  have hs := (hphys (y/x) (div_pos hy hx)).high_onsite x hx
    (show Anisotropic.FormFactors.realProduct (y/x) x < 1 by
      change realProduct (realSlice (y/x) x) < 1
      rwa [he])
  simpa only [he] using hs

/-- The common real physical realization of the two internally constructed
complex functions. Every covariance sum ranges over the entire lattice. -/
structure JointPhysicalConclusion (corrH corrL : CorrelationFamily)
    (mH mL : MagnetizationFamily) : Prop where
  high : ∀ x y : ℝ, 0 < x → 0 < y → realProduct (x,y) < 1 →
    Summable (corrH (x,y)) ∧
    FormFactors.highNormalizedBulk (complexify (x,y)) = (highCovarianceSum corrH (x,y):ℂ)
  low : ∀ x y : ℝ, 0 < x → 0 < y → 1 < realProduct (x,y) →
    Summable (fun v => corrL (x,y) v-magnetizationSq (x,y)) ∧
    FormFactors.lowNormalizedBulk (complexify (x,y)) = (lowCovarianceSum corrL (x,y):ℂ)
  low_onsite : ∀ x y : ℝ, 0 < x → 0 < y → 1 < realProduct (x,y) →
    corrL (x,y) (0,0)-magnetizationSq (x,y) = 1-magnetizationSq (x,y)
  high_onsite : ∀ x y : ℝ, 0 < x → 0 < y → realProduct (x,y) < 1 →
    corrH (x,y) (0,0) = 1
  high_field : ∀ J lam x : ℝ, 0 < J → 0 < lam → 0 < x →
    realProduct (realSlice lam x) < 1 →
    HasDerivAt (mH J (lam*J) (x/(2*J)))
      ((x/(2*J))*highCovarianceSum corrH (realSlice lam x)) 0 ∧
    (x/(2*J):ℂ)*FormFactors.highNormalizedBulk (complexify (realSlice lam x)) =
      (((x/(2*J))*highCovarianceSum corrH (realSlice lam x):ℝ):ℂ)
  low_field : ∀ J lam x : ℝ, 0 < J → 0 < lam → 0 < x →
    1 < realProduct (realSlice lam x) →
    HasDerivWithinAt (mL J (lam*J) (x/(2*J)))
      ((x/(2*J))*lowCovarianceSum corrL (realSlice lam x)) (Ioi 0) 0 ∧
    (x/(2*J):ℂ)*FormFactors.lowNormalizedBulk (complexify (realSlice lam x)) =
      (((x/(2*J))*lowCovarianceSum corrL (realSlice lam x):ℝ):ℂ)

theorem joint_physical_conclusion {corrH corrL : CorrelationFamily}
    {mH mL : MagnetizationFamily}
    (hphys : PublishedRealSpinFamily corrH corrL)
    (hfields : PublishedRealGibbsFamily corrH corrL mH mL) :
    JointPhysicalConclusion corrH corrL mH mL where
  high := fun _ _ hx hy hp => high_physical_identification hphys hx hy hp
  low := fun _ _ hx hy hp => low_physical_identification hphys hx hy hp
  low_onsite := fun _ _ hx hy hp => low_connected_onsite hphys hx hy hp
  high_onsite := fun _ _ hx hy hp => high_full_onsite hphys hx hy hp
  high_field := fun _ _ _ hJ hl hx hp => high_energy_field_derivative hphys hfields hJ hl hx hp
  low_field := fun _ _ _ hJ hl hx hp => low_energy_field_derivative hphys hfields hJ hl hx hp

end
end IsingBulk.Joint
