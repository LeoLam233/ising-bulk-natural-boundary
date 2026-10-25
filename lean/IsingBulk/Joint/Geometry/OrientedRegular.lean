import IsingBulk.Joint.Geometry.PrimeDensity

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic Transverse

/-- Exactly the two orientations used by the positive and negative edge models. -/
def OrientedPrimeJointFace (K : Coupling) : Prop :=
  S K ≠ 0 ∧ p K^2 ≠ 1 ∧ ∃ b : ℝ, |b| < 1 ∧ b ∈ primePhaseCosines ∧
    ((0 < (transferB K).im ∧ positiveParameter b K = 0) ∨
      (0 < (-transferB K).im ∧ negativeParameter b K = 0))

private theorem oriented_face_of_transfer {K : Coupling} {b eps : ℝ}
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (heps : eps = -1 ∨ eps = 1) (hB : 0 < eps*(transferB K).im)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) : OrientedPrimeJointFace K := by
  refine ⟨hS,hp,b,hb,hprime,?_⟩
  rcases heps with heps | heps
  · apply Or.inr
    refine ⟨by simpa [heps] using hB,?_⟩
    simp only [heps,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] at he
    dsimp [negativeParameter]
    linear_combination he
  · apply Or.inl
    refine ⟨by simpa [heps] using hB,?_⟩
    simp only [heps,Complex.ofReal_one,one_mul] at he
    dsimp [positiveParameter]
    linear_combination he

private theorem oriented_face_or_star {K : Coupling} {b eps : ℝ}
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (heps : eps = -1 ∨ eps = 1) (hB : (transferB K).im ≠ 0)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) :
    OrientedPrimeJointFace K ∨ OrientedPrimeJointFace (star K) := by
  have hene : eps ≠ 0 := by rcases heps with h | h <;> simp [h]
  rcases lt_or_gt_of_ne (mul_ne_zero hene hB) with hn | hp'
  · apply Or.inr
    have hS' : S (star K) ≠ 0 := by simpa using hS
    have hp'' : p (star K)^2 ≠ 1 := by
      intro hh
      apply hp
      have hh' := congrArg (starRingEnd ℂ) hh
      simpa using hh'
    have he' : transferC (star K) = (b:ℂ)+(eps:ℂ)*transferB (star K) := by
      have hh := congrArg (starRingEnd ℂ) he
      simpa using hh
    exact oriented_face_of_transfer hS' hp'' hb hprime heps
      (by simp only [transferB_star,Complex.star_def,Complex.conj_im]; nlinarith) he'
  · exact Or.inl (oriented_face_of_transfer hS hp hb hprime heps hp' he)

private theorem transfer_of_unsquared {K : Coupling} {a b : ℝ} (hS : S K ≠ 0)
    (he : A K = S K*(a:ℂ)+T K*(b:ℂ)) :
    transferC K = (a:ℂ)+(b:ℂ)*transferB K := by
  unfold transferC transferB
  rw [he]
  field_simp

/-- No regular orientation is discarded: conjugation and axis exchange reduce
all selected points to one of the two genuine edge models. -/
theorem primeRegular_oriented_cases {K : Coupling} (hK : IsPrimeRegularJointEdge K) :
    OrientedPrimeJointFace K ∨ OrientedPrimeJointFace (star K) ∨
      OrientedPrimeJointFace K.swap ∨ OrientedPrimeJointFace (star K.swap) := by
  obtain ⟨hr,a,b,he,hend⟩ := hK
  rcases hend with hend | hend
  · have hrs := swap_isRegularJointEdge hr
    have he' : A K.swap = S K.swap*(b:ℂ)+T K.swap*(a:ℂ) := by
      simpa [A,S,T,mul_comm,add_comm] using he
    have hh := oriented_face_or_star hrs.2.1 hrs.2.2.2.2.1 hend.2.1 hend.2.2 hend.1
      (transferB_im_ne_of_regular hrs) (transfer_of_unsquared hrs.2.1 he')
    exact Or.inr (Or.inr hh)
  · have hh := oriented_face_or_star hr.2.1 hr.2.2.2.2.1 hend.1 hend.2.1 hend.2.2
      (transferB_im_ne_of_regular hr) (transfer_of_unsquared hr.2.1 he)
    rcases hh with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end
end IsingBulk.Joint
