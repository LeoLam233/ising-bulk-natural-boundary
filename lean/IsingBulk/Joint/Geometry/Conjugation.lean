import IsingBulk.Joint.Geometry.Swap

namespace IsingBulk.Joint
noncomputable section
open Set

def couplingConjugation : Coupling ≃ₜ Coupling where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star

@[simp] theorem S_star (K : Coupling) : S (star K) = star (S K) := by
  simp [S,Complex.sinh_conj]
@[simp] theorem T_star (K : Coupling) : T (star K) = star (T K) := by
  simp [T,Complex.sinh_conj]
@[simp] theorem A_star (K : Coupling) : A (star K) = star (A K) := by
  simp [A,Complex.cosh_conj]
@[simp] theorem p_star (K : Coupling) : p (star K) = star (p K) := by
  simp [p]
@[simp] theorem transferC_star (K : Coupling) : transferC (star K) = star (transferC K) := by
  simp [transferC]
@[simp] theorem transferB_star (K : Coupling) : transferB (star K) = star (transferB K) := by
  simp [transferB]

theorem star_highDomain_iff (K : Coupling) : star K ∈ highDomain ↔ K ∈ highDomain := by
  simp [highDomain]
theorem star_lowDomain_iff (K : Coupling) : star K ∈ lowDomain ↔ K ∈ lowDomain := by
  simp [lowDomain]

theorem star_frontier_high_iff (K : Coupling) : star K ∈ frontier highDomain ↔ K ∈ frontier highDomain := by
  have he : couplingConjugation ⁻¹' highDomain = highDomain := Set.ext star_highDomain_iff
  change K ∈ couplingConjugation ⁻¹' frontier highDomain ↔ _
  rw [couplingConjugation.preimage_frontier,he]
theorem star_frontier_low_iff (K : Coupling) : star K ∈ frontier lowDomain ↔ K ∈ frontier lowDomain := by
  have he : couplingConjugation ⁻¹' lowDomain = lowDomain := Set.ext star_lowDomain_iff
  change K ∈ couplingConjugation ⁻¹' frontier lowDomain ↔ _
  rw [couplingConjugation.preimage_frontier,he]

theorem star_isRegularJointEdge {K : Coupling} (hK : IsRegularJointEdge K) :
    IsRegularJointEdge (star K) := by
  obtain ⟨hb,hS,hT,hd,hp,a,ha,b,hb',he,hend⟩ := hK
  refine ⟨?_,by simpa using hS,by simpa using hT,?_,?_,a,ha,b,hb',?_,hend⟩
  · rcases hb with h | h
    · exact Or.inl ((star_frontier_high_iff K).mpr h)
    · exact Or.inr ((star_frontier_low_iff K).mpr h)
  · have hi : (star (S (star K))*T (star K)).im = -(star (S K)*T K).im := by
      simp only [S_star,T_star,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
      ring
    rw [hi]
    exact neg_ne_zero.mpr hd
  · intro h
    apply hp
    have hh := congrArg (starRingEnd ℂ) h
    simpa only [p_star,map_pow,map_one,starRingEnd_apply,star_star] using hh
  · have hh := congrArg (starRingEnd ℂ) he
    simpa using hh

end
end IsingBulk.Joint
