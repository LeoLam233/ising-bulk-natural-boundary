import IsingBulk.HT22.Finite.RemainderIdentity
import IsingBulk.HT22.Tail.LocalizedObservable
namespace IsingBulk.HT22.Finite
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22 IsingBulk.HT22.Physical
open IsingBulk.HT22.Physical.FiniteAssembly IsingBulk.HT22.Geometry
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Global function equality with the new actual localized transport
observable, not merely equality of zeroth radial values. -/
theorem separated_remainder_eq_observable (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δ R : ℝ} (hR : 0<R)
    (τ : ℝ) (r : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δ r)
    (rem : (Fin n → ℝ) → ℝ)
    (hfar : ∀ θ∈signedRightRegion (constraintAngle negative) d B δ,rem θ≠0 →
      R<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ))) :
    localizedRightIntegral negative n τ B.p B.m r rem=
      Tail.localizedObservable negative n d B τ r (separatedAmbientRemainder R rem) := by
  funext t
  unfold localizedRightIntegral Tail.localizedObservable
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro θ hθ
  have he := separatedAmbientRemainder_weighted_lift_eq d B hR r hcut (constraintAngle negative) rem hfar θ hθ
  dsimp only at he ⊢
  rw [preferredCellWeight_lift .right B.delta preferredPopulationCutoff B.p B.m r B.periodic B.m_periodic hcut.2.2.2.1] at he ⊢
  change _ = (_*_) * _
  simpa only [Physical.constrainedAngles,constrainedAtTotal] using
    congrArg (fun z : ℂ => z*bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) he.symm
end
end IsingBulk.HT22.Finite
