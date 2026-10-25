import IsingBulk.Joint.Geometry.HighBoundaryParameters
import IsingBulk.Joint.Geometry.Swap

namespace IsingBulk.Joint
noncomputable section
open Set

def regularJointEdges : Set Coupling := {K | IsRegularJointEdge K}

theorem high_first_face_mem_closure_regular {K : Coupling} (hK : K ∈ frontier highDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = Real.cos K.1.im) :
    K ∈ closure regularJointEdges := by
  obtain ⟨sgn,a,hs,ha,he⟩ := high_first_face_parameter_exists (frontier_subset_closure hK) hface
  have hv := realProduct_le_one_mem_closure_regular (realProduct_le_one_of_closure_high (frontier_subset_closure hK))
  have hparam : ((K.1.re,K.2.re),a) ∈ closure (regularRealSubcritical ×ˢ Ioo (-1:ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (-1:ℝ)≠1)]
    exact ⟨hv,abs_le.mp ha⟩
  have hm : MapsTo (highFaceParameter sgn) (regularRealSubcritical ×ˢ Ioo (-1:ℝ) 1)
      regularJointEdges := by
    intro q hq
    exact highFaceParameter_regular hs hq.1 (abs_lt.mpr hq.2)
  have hh := hm.closure (highFaceParameter_continuous sgn) hparam
  rwa [he] at hh

/-- Genuine density on the entire C² high-temperature boundary, including its
axes, corners, collapsed fibers, and collinear strata. -/
theorem frontier_high_subset_closure_regularJointEdges :
    frontier highDomain ⊆ closure regularJointEdges := by
  intro K hK
  rcases high_boundary_active_face hK with h | h
  · exact high_first_face_mem_closure_regular hK h
  · have hs := (swap_frontier_high_iff K).mpr hK
    have hf : faceRatio1 (K.swap.1.re,K.swap.2.re) = Real.cos K.swap.1.im := h
    have hd := high_first_face_mem_closure_regular hs hf
    have hm : MapsTo Prod.swap regularJointEdges regularJointEdges :=
      fun _ h => swap_isRegularJointEdge h
    simpa only [Prod.swap_swap] using hm.closure continuous_swap hd

end
end IsingBulk.Joint
