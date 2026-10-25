import IsingBulk.Joint.Isotropic.DeckInvariance
import IsingBulk.Joint.FormFactors.NormalizedRestriction
import IsingBulk.Anisotropic.Final.IsotropicHighTheorem
import IsingBulk.Anisotropic.Final.IsotropicLowTheorem

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

/-- The actual joint HT function, not an independently postulated slice germ,
descends to the complete preexisting normalized odd sum. -/
theorem joint_high_isotropic_identity {z : ℂ} (hz : z ∈ omegaH 1) :
    FormFactors.highNormalizedBulk (ratioSlice 1 z) =
      IsingBulk.HT.Final.interiorFullBulk (Complex.sinh z) := by
  rw [FormFactors.highNormalizedBulk_ratioSlice (by norm_num) hz]
  exact highNormalizedBulk_one_eqOn hz

/-- The actual joint LT function descends to the complete connected normalized
even sum. The real onsite input is the same physical interface as C001. -/
theorem joint_low_isotropic_identity
    {corrH corrL : ℝ → Anisotropic.FormFactors.LatticeSite → ℝ}
    (hphys : Anisotropic.FormFactors.PublishedRealSpinFormFactors 1 corrH corrL)
    {z : ℂ} (hz : z ∈ omegaL 1) :
    FormFactors.lowNormalizedBulk (ratioSlice 1 z) =
      IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z) := by
  rw [FormFactors.lowNormalizedBulk_ratioSlice (by norm_num) hz]
  exact lowNormalizedBulk_one_eqOn hphys hz

/-- The high descendant is recovered by the actual holomorphic inverse of sinh. -/
theorem high_descendant_on_disk {s : ℂ} (hs : ‖s‖ < 1) :
    FormFactors.highNormalizedBulk (ratioSlice 1 (IsingBulk.Final.arsinhRight s)) =
      IsingBulk.HT.Final.interiorFullBulk s := by
  rw [joint_high_isotropic_identity (arsinhRight_mem_high hs),
    sinh_arsinhRight_strip ((Complex.abs_im_le_norm s).trans_lt hs)]

/-- Every exterior point is attained and all lifts give the very same reduced
response. No globally single-valued exterior inverse temperature is used. -/
theorem low_descendant_on_exterior
    {corrH corrL : ℝ → Anisotropic.FormFactors.LatticeSite → ℝ}
    (hphys : Anisotropic.FormFactors.PublishedRealSpinFormFactors 1 corrH corrL)
    {s : ℂ} (hs : 1 < ‖s‖) :
    (∃ z ∈ omegaL 1, Complex.sinh z = s) ∧
    ∀ z ∈ omegaL 1, Complex.sinh z = s →
      FormFactors.lowNormalizedBulk (ratioSlice 1 z) = IsingBulk.Tail.exteriorNormalizedBulk s := by
  refine ⟨sinh_surjOn_low hs,?_⟩
  intro z hz he
  rw [joint_low_isotropic_identity hphys hz,he]

end
end IsingBulk.Joint
