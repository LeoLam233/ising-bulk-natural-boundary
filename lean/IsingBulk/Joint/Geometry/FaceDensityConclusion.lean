import IsingBulk.Joint.Geometry.OrientedRegular

/-! Explicit local-face density, retaining the physical frontier, endpoint and
fixed anisotropy. This is stronger than density only in the whole boundary. -/
namespace IsingBulk.Joint
noncomputable section
open Set

private theorem star_frontier {D : Set Coupling} (hD : D=highDomain ∨ D=lowDomain)
    {K : Coupling} (hK : K∈frontier D) : star K∈frontier D := by
  rcases hD with rfl | rfl
  · exact (star_frontier_high_iff K).mpr hK
  · exact (star_frontier_low_iff K).mpr hK

private theorem swap_frontier {D : Set Coupling} (hD : D=highDomain ∨ D=lowDomain)
    {K : Coupling} (hK : K∈frontier D) : K.swap∈frontier D := by
  rcases hD with rfl | rfl
  · exact (swap_frontier_high_iff K).mpr hK
  · exact (swap_frontier_low_iff K).mpr hK

/-- At every regular transfer face, selected phases are dense while B remains
exactly fixed, with both endpoint signs and both half-plane orientations. -/
theorem face_mem_closure_selected_fixed_B {D : Set Coupling}
    (hD : D=highDomain ∨ D=lowDomain) {K : Coupling} {b eps : ℝ}
    (hK : K∈frontier D) (hS : S K≠0) (hp : p K^2≠1) (hb : |b|<1)
    (heps : eps = -1 ∨ eps = 1) (hB : (transferB K).im≠0)
    (he : transferC K=(b:ℂ)+(eps:ℂ)*transferB K) :
    K∈closure (selectedTransferFace D (transferB K) eps) := by
  have hene : eps≠0 := by rcases heps with h | h <;> simp [h]
  rcases lt_or_gt_of_ne (mul_ne_zero hene hB) with hn | hp'
  · have hS' : S (star K)≠0 := by simpa using hS
    have hp'' : p (star K)^2≠1 := by
      intro hh
      apply hp
      have hh' := congrArg (starRingEnd ℂ) hh
      simpa using hh'
    have he' : transferC (star K)=(b:ℂ)+(eps:ℂ)*transferB (star K) := by
      have hh := congrArg (starRingEnd ℂ) he
      simpa using hh
    have hB' : 0<eps*(transferB (star K)).im := by
      simp only [transferB_star,Complex.star_def,Complex.conj_im]
      nlinarith
    have hcl := oriented_face_mem_closure_prime_fixed_B hD (star_frontier hD hK)
      hS' hp'' hb heps hB' he'
    have hm : MapsTo star (selectedTransferFace D (transferB (star K)) eps)
        (selectedTransferFace D (transferB K) eps) := by
      intro L hL
      refine ⟨star_frontier hD hL.1,star_isPrimeRegularJointEdge hL.2.1,?_,?_⟩
      · have hh := congrArg (starRingEnd ℂ) hL.2.2.1
        simpa using hh
      · obtain ⟨t,ht,hprime,htC⟩ := hL.2.2.2
        refine ⟨t,ht,hprime,?_⟩
        have hh := congrArg (starRingEnd ℂ) htC
        simpa using hh
    simpa only [star_star] using hm.closure continuous_star hcl
  · exact oriented_face_mem_closure_prime_fixed_B hD hK hS hp hb heps hp' he

/-- The neighborhood form makes the local regular patch quantifier explicit. -/
theorem selected_fixed_B_in_every_neighborhood {D : Set Coupling}
    (hD : D=highDomain ∨ D=lowDomain) {K : Coupling} {b eps : ℝ}
    (hK : K∈frontier D) (hS : S K≠0) (hp : p K^2≠1) (hb : |b|<1)
    (heps : eps = -1 ∨ eps = 1) (hB : (transferB K).im≠0)
    (he : transferC K=(b:ℂ)+(eps:ℂ)*transferB K)
    (U : Set Coupling) (hU : IsOpen U) (hKU : K∈U) :
    ∃L∈U,L∈selectedTransferFace D (transferB K) eps :=
  mem_closure_iff.mp (face_mem_closure_selected_fixed_B hD hK hS hp hb heps hB he) U hU hKU

private theorem transfer_of_unsquared {K : Coupling} {a b : ℝ} (hS : S K≠0)
    (he : A K=S K*(a:ℂ)+T K*(b:ℂ)) :
    transferC K=(a:ℂ)+(b:ℂ)*transferB K := by
  unfold transferC transferB
  rw [he]
  field_simp

/-- Every regular boundary point has a selected dense face in its actual
transfer chart or the exchanged transfer chart, with fixed anisotropy. -/
theorem regular_face_selected_fixed_B {D : Set Coupling}
    (hD : D=highDomain ∨ D=lowDomain) {K : Coupling}
    (hK : K∈frontier D) (hr : IsRegularJointEdge K) :
    ∃eps : ℝ,(eps = -1 ∨ eps = 1) ∧
      (K∈closure (selectedTransferFace D (transferB K) eps) ∨
        K.swap∈closure (selectedTransferFace D (transferB K.swap) eps)) := by
  have hB := transferB_im_ne_of_regular hr
  have hrs := swap_isRegularJointEdge hr
  obtain ⟨_,hS,hT,_,hp,a,_,b,_,he,hend⟩ := hr
  rcases hend with hend | hend
  · have he' : A K.swap=S K.swap*(b:ℂ)+T K.swap*(a:ℂ) := by
      simpa [A,S,T,mul_comm,add_comm] using he
    exact ⟨a,hend.1,Or.inr (face_mem_closure_selected_fixed_B hD (swap_frontier hD hK)
      hrs.2.1 hrs.2.2.2.2.1 (abs_lt.mpr hend.2) hend.1 (transferB_im_ne_of_regular hrs)
      (transfer_of_unsquared hrs.2.1 he'))⟩
  · exact ⟨b,hend.2,Or.inl (face_mem_closure_selected_fixed_B hD hK hS hp
      (abs_lt.mpr hend.1) hend.2 hB (transfer_of_unsquared hS he))⟩

/-- Explicit same-physical-face density for the final J4 conjunction. -/
structure JointFaceDensityConclusion : Prop where
  fixed_B : ∀(D : Set Coupling), D=highDomain ∨ D=lowDomain →
    ∀(K : Coupling) (b eps : ℝ), K∈frontier D → S K≠0 → p K^2≠1 → |b|<1 →
    (eps = -1 ∨ eps = 1) → (transferB K).im≠0 →
    transferC K=(b:ℂ)+(eps:ℂ)*transferB K →
    ∀U : Set Coupling,IsOpen U → K∈U → ∃L∈U,L∈selectedTransferFace D (transferB K) eps
  every_regular_face : ∀(D : Set Coupling), D=highDomain ∨ D=lowDomain →
    ∀K∈frontier D,IsRegularJointEdge K →
    ∃eps : ℝ,(eps = -1 ∨ eps = 1) ∧
      (K∈closure (selectedTransferFace D (transferB K) eps) ∨
        K.swap∈closure (selectedTransferFace D (transferB K.swap) eps))

theorem joint_face_density_conclusion : JointFaceDensityConclusion where
  fixed_B := fun _ hD _ _ _ hK hS hp hb heps hB he U hU hKU =>
    selected_fixed_B_in_every_neighborhood hD hK hS hp hb heps hB he U hU hKU
  every_regular_face := fun _ hD _ hK hr=>regular_face_selected_fixed_B hD hK hr

end
end IsingBulk.Joint
