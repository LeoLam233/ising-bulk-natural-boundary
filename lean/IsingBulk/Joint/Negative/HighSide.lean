import IsingBulk.Joint.Negative.Normalization
import IsingBulk.Joint.Transverse.NegativeLocalSide

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.RegularEdges
open scoped Topology

theorem UpperNormalization.high_upper_radius {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (D : UpperNormalization curve amp b) (hb : |b|<1)
    (hK : curve 0∈frontier highDomain) (hp : p (curve 0)^2≠1) :
    ∃r : ℝ,0<r ∧ r≤D.radius ∧ ∀u∈upperBall r,D.Z u∈highDomain := by
  have h0 : (0:ℂ)∈ball 0 D.radius := mem_ball_self D.radius_pos
  have hZ0 : D.Z 0=curve 0 := by simpa only [D.f_zero] using D.curve_eq.eq_of_nhds.symm
  have hnegative : Transverse.negativeParameter b (D.Z 0)=0 := by
    unfold Transverse.negativeParameter
    rw [D.edge 0 h0,add_zero,sub_self]
  obtain ⟨W,hW,hKW,_,hside⟩ := Transverse.negativeFace_high_side
    (by rwa [hZ0]) (D.S_ne 0 h0) (by rwa [hZ0])
    (by simpa only [negativeChartB,transferB,neg_div] using D.B_pos 0 h0) hb hnegative
  have he := (D.Z_analytic 0 h0).continuousAt.tendsto.eventually (hW.mem_nhds hKW)
  obtain ⟨r0,hr0,hrW⟩ := Metric.mem_nhds_iff.mp he
  let r := min r0 D.radius
  have hr : 0<r := lt_min hr0 D.radius_pos
  refine ⟨r,hr,min_le_right _ _,?_⟩
  intro u hu
  have hu0 : u∈ball 0 r0 := ball_subset_ball (min_le_left _ _) hu.1
  have huD : u∈ball 0 D.radius := ball_subset_ball (min_le_right _ _) hu.1
  apply (hside _ (hrW hu0)).mpr
  simpa only [Transverse.negativeParameter,D.edge u huD,add_sub_cancel_left,Set.mem_ofPred_eq] using hu.2

end
end IsingBulk.Joint.Negative
