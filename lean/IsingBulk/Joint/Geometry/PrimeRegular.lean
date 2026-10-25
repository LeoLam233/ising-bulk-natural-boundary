import IsingBulk.Joint.Geometry.Conjugation
import IsingBulk.Joint.Geometry.TransferRegular
import IsingBulk.Anisotropic.Geometry.PrimePhases

namespace IsingBulk.Joint
noncomputable section
open Set
open IsingBulk.Anisotropic

/-- A genuine regular edge with a selected prime phase in its free real coordinate. -/
def IsPrimeRegularJointEdge (K : Coupling) : Prop :=
  IsRegularJointEdge K ∧ ∃ a b : ℝ, A K = S K*(a:ℂ)+T K*(b:ℂ) ∧
    (((a = -1 ∨ a = 1) ∧ |b| < 1 ∧ b ∈ primePhaseCosines) ∨
      (|a| < 1 ∧ a ∈ primePhaseCosines ∧ (b = -1 ∨ b = 1)))

def primeRegularJointEdges : Set Coupling := {K | IsPrimeRegularJointEdge K}

theorem primeRegularJointEdge_of_transfer {K : Coupling} {b eps : ℝ}
    (hK : IsRegularJointEdge K) (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (heps : eps = -1 ∨ eps = 1)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) : IsPrimeRegularJointEdge K := by
  have heq : A K = S K*(b:ℂ)+T K*(eps:ℂ) := by
    unfold transferC transferB at he
    field_simp [hK.2.1] at he
    linear_combination he
  exact ⟨hK,b,eps,heq,Or.inr ⟨hb,hprime,heps⟩⟩

theorem swap_isPrimeRegularJointEdge {K : Coupling} (hK : IsPrimeRegularJointEdge K) :
    IsPrimeRegularJointEdge K.swap := by
  obtain ⟨hr,a,b,he,hend⟩ := hK
  refine ⟨swap_isRegularJointEdge hr,b,a,by simpa [A,S,T,mul_comm,add_comm] using he,?_⟩
  rcases hend with h | h
  · exact Or.inr ⟨h.2.1,h.2.2,h.1⟩
  · exact Or.inl ⟨h.2.2,h.1,h.2.1⟩

theorem star_isPrimeRegularJointEdge {K : Coupling} (hK : IsPrimeRegularJointEdge K) :
    IsPrimeRegularJointEdge (star K) := by
  obtain ⟨hr,a,b,he,hend⟩ := hK
  refine ⟨star_isRegularJointEdge hr,a,b,?_,hend⟩
  have hh := congrArg (starRingEnd ℂ) he
  simpa using hh

end
end IsingBulk.Joint
