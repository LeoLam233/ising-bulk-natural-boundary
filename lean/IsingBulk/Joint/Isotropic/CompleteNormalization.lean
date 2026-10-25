import IsingBulk.Joint.Isotropic.PhysicalDescent
import IsingBulk.Joint.PhysicalField.RealFamily

namespace IsingBulk.Joint
noncomputable section
open Set Anisotropic

/-- The descendant is the complete normalized ODD full-site series, not a
diagonal susceptibility or a truncated order. Zero is supplied by the separately
proved removable-origin theorem. -/
theorem high_descendant_complete_odd_formula {s : ℂ} (hs : s≠0) :
    IsingBulk.HT.Final.interiorFullBulk s = (1-s^4)^(1/4:ℂ)/s *
      ∑' n : ℕ, IsingBulk.HT.Final.exteriorOddTerm n (s⁻¹) := by
  unfold IsingBulk.HT.Final.interiorFullBulk IsingBulk.HT.Final.interiorFourthFactor
  rw [IsingBulk.HT.Final.regularInteriorSeries_eq hs]
  unfold IsingBulk.HT.Final.interiorRawSeries IsingBulk.HT.Final.exteriorOddSeries
  ring

/-- The exact connected onsite term is retained in the normalized LT
descendant. The remaining terms are the complete positive-even offsite series;
its equivalence to the full-site joint series is proved by actual descent. -/
theorem low_descendant_complete_connected_formula (s : ℂ) :
    IsingBulk.Tail.exteriorNormalizedBulk s =
      1-(1-(s^4)⁻¹)^(1/4:ℂ) + 2*(1-(s^4)⁻¹)^(1/4:ℂ) *
        ∑' n : ℕ, IsingBulk.Tail.exteriorEvenTerm n s := rfl

/-- This is the same even descendant expressed instead by the literal FULL
site contour coefficients on any of its physical lifts, with no zero-particle
vacuum term. It is not a postulated equality of two analytic continuations. -/
theorem low_descendant_complete_fullsite_formula
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {z : ℂ} (hz : z∈omegaL 1) :
    IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z) =
      FormFactors.lowPrefactor (ratioSlice 1 z) *
        ∑' n : ℕ, p (ratioSlice 1 z)^(n+1) *
          FormFactors.unscaledFullCoefficient (2*n+2) (ratioSlice 1 z) :=
  (joint_low_isotropic_identity (hphys 1 (by norm_num)) hz).symm

theorem high_descendant_complete_fullsite_formula
    {z : ℂ} (hz : z∈omegaH 1) :
    IsingBulk.HT.Final.interiorFullBulk (Complex.sinh z) =
      FormFactors.highPrefactor (ratioSlice 1 z) *
        ∑' n : ℕ, p (ratioSlice 1 z)^n *
          FormFactors.unscaledFullCoefficient (2*n+1) (ratioSlice 1 z) :=
  (joint_high_isotropic_identity hz).symm

end
end IsingBulk.Joint
