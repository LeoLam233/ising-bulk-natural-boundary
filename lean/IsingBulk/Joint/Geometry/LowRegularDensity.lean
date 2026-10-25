import IsingBulk.Joint.Geometry.LowBoundaryParameters
import IsingBulk.Joint.Geometry.HighRegularDensity

namespace IsingBulk.Joint
noncomputable section
open Set

theorem low_first_face_mem_closure_regular {K : Coupling} (hK : K ∈ frontier lowDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = |Real.cos K.1.im|) :
    K ∈ closure regularJointEdges := by
  obtain ⟨k,l,sgn,τ,a,hs,hτ,ha,he⟩ := low_first_face_parameter_exists hK hface
  obtain ⟨hx,hu,_,_⟩ := closure_low_bounds (frontier_subset_closure hK)
  have hv := nonnegative_realProduct_mem_closure_positive hx hu (realProduct_le_one_of_frontier_low hK)
  have hparam : ((K.1.re,K.2.re),a) ∈ closure (positiveRealSubcritical ×ˢ Ioo (-1:ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (-1:ℝ)≠1)]
    exact ⟨hv,abs_le.mp ha⟩
  have hm : MapsTo (lowFaceParameter k l sgn τ) (positiveRealSubcritical ×ˢ Ioo (-1:ℝ) 1)
      regularJointEdges := by
    intro q hq
    exact lowFaceParameter_regular k l hs hτ hq.1 (abs_lt.mpr hq.2)
  have hh := hm.closure (lowFaceParameter_continuous k l sgn τ) hparam
  rwa [he] at hh

/-- Density on every low-temperature boundary stratum, retaining all imaginary periods. -/
theorem frontier_low_subset_closure_regularJointEdges :
    frontier lowDomain ⊆ closure regularJointEdges := by
  intro K hK
  rcases low_boundary_active_face hK with h | h
  · exact low_first_face_mem_closure_regular hK h
  · have hs := (swap_frontier_low_iff K).mpr hK
    have hf : faceRatio1 (K.swap.1.re,K.swap.2.re) = |Real.cos K.swap.1.im| := h
    have hd := low_first_face_mem_closure_regular hs hf
    have hm : MapsTo Prod.swap regularJointEdges regularJointEdges :=
      fun _ h => swap_isRegularJointEdge h
    simpa only [Prod.swap_swap] using hm.closure continuous_swap hd

end
end IsingBulk.Joint
