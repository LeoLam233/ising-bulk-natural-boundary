import IsingBulk.Joint.Geometry.RegularFace

namespace IsingBulk.Joint
noncomputable section
open Set

theorem swap_highDomain_iff (K : Coupling) : K.swap ∈ highDomain ↔ K ∈ highDomain := by
  simp only [highDomain,Set.mem_ofPred_eq,Prod.fst_swap,Prod.snd_swap]
  tauto

theorem swap_lowDomain_iff (K : Coupling) : K.swap ∈ lowDomain ↔ K ∈ lowDomain := by
  simp only [lowDomain,Set.mem_ofPred_eq,Prod.fst_swap,Prod.snd_swap]
  tauto

theorem swap_frontier_high_iff (K : Coupling) : K.swap ∈ frontier highDomain ↔ K ∈ frontier highDomain := by
  let e := Homeomorph.prodComm ℂ ℂ
  have he : e ⁻¹' highDomain = highDomain := Set.ext swap_highDomain_iff
  change K ∈ e ⁻¹' frontier highDomain ↔ _
  rw [e.preimage_frontier,he]

theorem swap_frontier_low_iff (K : Coupling) : K.swap ∈ frontier lowDomain ↔ K ∈ frontier lowDomain := by
  let e := Homeomorph.prodComm ℂ ℂ
  have he : e ⁻¹' lowDomain = lowDomain := Set.ext swap_lowDomain_iff
  change K ∈ e ⁻¹' frontier lowDomain ↔ _
  rw [e.preimage_frontier,he]

theorem swap_isRegularJointEdge {K : Coupling} (hK : IsRegularJointEdge K) :
    IsRegularJointEdge K.swap := by
  obtain ⟨hb,hS,hT,hd,hp,a,ha,b,hb',he,hend⟩ := hK
  refine ⟨?_,hT,hS,?_,?_,b,hb',a,ha,?_,?_⟩
  · rcases hb with h | h
    · exact Or.inl ((swap_frontier_high_iff K).mpr h)
    · exact Or.inr ((swap_frontier_low_iff K).mpr h)
  · have hi : (star (S K.swap)*T K.swap).im = -(star (S K)*T K).im := by
      simp only [S,T,Prod.fst_swap,Prod.snd_swap,Complex.mul_im,Complex.star_def,
        Complex.conj_re,Complex.conj_im]
      ring
    rw [hi]
    exact neg_ne_zero.mpr hd
  · simpa [p,S,T,mul_comm] using hp
  · simpa [A,S,T,mul_comm,add_comm] using he
  · rcases hend with h | h
    · exact Or.inr ⟨h.2,h.1⟩
    · exact Or.inl ⟨h.2,h.1⟩

theorem swap_isRegularJointEdge_iff (K : Coupling) :
    IsRegularJointEdge K.swap ↔ IsRegularJointEdge K :=
  ⟨fun h => by simpa using swap_isRegularJointEdge h,swap_isRegularJointEdge⟩

end
end IsingBulk.Joint
