import IsingBulk.Joint.Geometry.OrientedPrimeDensity
import IsingBulk.Joint.Geometry.LowRegularDensity

namespace IsingBulk.Joint
noncomputable section
open Set

private theorem star_frontier_physical {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} (hK : K ∈ frontier D) : star K ∈ frontier D := by
  rcases hD with rfl | rfl
  · exact (star_frontier_high_iff K).mpr hK
  · exact (star_frontier_low_iff K).mpr hK

private theorem swap_frontier_physical {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} (hK : K ∈ frontier D) : K.swap ∈ frontier D := by
  rcases hD with rfl | rfl
  · exact (swap_frontier_high_iff K).mpr hK
  · exact (swap_frontier_low_iff K).mpr hK

theorem face_mem_closure_prime {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} {b eps : ℝ} (hK : K ∈ frontier D)
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1)
    (heps : eps = -1 ∨ eps = 1) (hB : (transferB K).im ≠ 0)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) :
    K ∈ closure (frontier D ∩ primeRegularJointEdges) := by
  have hene : eps ≠ 0 := by rcases heps with h | h <;> simp [h]
  rcases lt_or_gt_of_ne (mul_ne_zero hene hB) with hnegative | hpositive
  · have hSstar : S (star K) ≠ 0 := by simpa using hS
    have hpstar : p (star K)^2 ≠ 1 := by
      intro hh
      apply hp
      have hh' := congrArg (starRingEnd ℂ) hh
      simpa using hh'
    have hestar : transferC (star K) = (b:ℂ)+(eps:ℂ)*transferB (star K) := by
      have hh := congrArg (starRingEnd ℂ) he
      simpa using hh
    have hBstar : 0 < eps*(transferB (star K)).im := by
      simp only [transferB_star,Complex.star_def,Complex.conj_im]
      nlinarith
    have hcl := oriented_face_mem_closure_prime hD (star_frontier_physical hD hK)
      hSstar hpstar hb heps hBstar hestar
    have hm : MapsTo star (frontier D ∩ primeRegularJointEdges) (frontier D ∩ primeRegularJointEdges) :=
      fun _ h => ⟨star_frontier_physical hD h.1,star_isPrimeRegularJointEdge h.2⟩
    simpa only [star_star] using hm.closure continuous_star hcl
  · exact oriented_face_mem_closure_prime hD hK hS hp hb heps hpositive he

private theorem transfer_eq_of_unsquared {K : Coupling} {a b : ℝ} (hS : S K ≠ 0)
    (he : A K = S K*(a:ℂ)+T K*(b:ℂ)) :
    transferC K = (a:ℂ)+(b:ℂ)*transferB K := by
  unfold transferC transferB
  rw [he]
  field_simp

/-- Every regular point is approached by selected points on the same physical boundary. -/
theorem regular_mem_closure_prime {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} (hK : K ∈ frontier D) (hr : IsRegularJointEdge K) :
    K ∈ closure (frontier D ∩ primeRegularJointEdges) := by
  have hB := transferB_im_ne_of_regular hr
  have hrs := swap_isRegularJointEdge hr
  obtain ⟨_,hS,hT,_,hp,a,_,b,_,he,hend⟩ := hr
  rcases hend with hend | hend
  · have he' : A K.swap = S K.swap*(b:ℂ)+T K.swap*(a:ℂ) := by
      simpa [A,S,T,mul_comm,add_comm] using he
    have hcl := face_mem_closure_prime hD (swap_frontier_physical hD hK)
      hrs.2.1 hrs.2.2.2.2.1 (abs_lt.mpr hend.2) hend.1 (transferB_im_ne_of_regular hrs)
      (transfer_eq_of_unsquared hrs.2.1 he')
    have hm : MapsTo Prod.swap (frontier D ∩ primeRegularJointEdges) (frontier D ∩ primeRegularJointEdges) :=
      fun _ h => ⟨swap_frontier_physical hD h.1,swap_isPrimeRegularJointEdge h.2⟩
    simpa only [Prod.swap_swap] using hm.closure continuous_swap hcl
  · exact face_mem_closure_prime hD hK hS hp (abs_lt.mpr hend.1) hend.2 hB
      (transfer_eq_of_unsquared hS he)


private theorem high_first_face_mem_closure_prime {K : Coupling} (hK : K ∈ frontier highDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = Real.cos K.1.im) :
    K ∈ closure (frontier highDomain ∩ primeRegularJointEdges) := by
  obtain ⟨sgn,a,hs,ha,he⟩ := high_first_face_parameter_exists (frontier_subset_closure hK) hface
  have hv := realProduct_le_one_mem_closure_regular
    (realProduct_le_one_of_closure_high (frontier_subset_closure hK))
  have hparam : ((K.1.re,K.2.re),a) ∈ closure (regularRealSubcritical ×ˢ Ioo (-1:ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
    exact ⟨hv,abs_le.mp ha⟩
  have hm : MapsTo (highFaceParameter sgn) (regularRealSubcritical ×ˢ Ioo (-1:ℝ) 1)
      (closure (frontier highDomain ∩ primeRegularJointEdges)) := by
    intro q hq
    exact regular_mem_closure_prime (Or.inl rfl)
      (highFaceParameter_frontier hs hq.1 (abs_lt.mpr hq.2))
      (highFaceParameter_regular hs hq.1 (abs_lt.mpr hq.2))
  have hh := hm.closure (highFaceParameter_continuous sgn) hparam
  simpa only [closure_closure,he] using hh

/-- Selected prime phases are dense on the entire actual high-temperature boundary. -/
theorem frontier_high_subset_closure_primeRegularJointEdges :
    frontier highDomain ⊆ closure (frontier highDomain ∩ primeRegularJointEdges) := by
  intro K hK
  rcases high_boundary_active_face hK with h | h
  · exact high_first_face_mem_closure_prime hK h
  · have hs := (swap_frontier_high_iff K).mpr hK
    have hf : faceRatio1 (K.swap.1.re,K.swap.2.re) = Real.cos K.swap.1.im := h
    have hd := high_first_face_mem_closure_prime hs hf
    have hm : MapsTo Prod.swap (frontier highDomain ∩ primeRegularJointEdges)
        (frontier highDomain ∩ primeRegularJointEdges) :=
      fun _ h => ⟨(swap_frontier_high_iff _).mpr h.1,swap_isPrimeRegularJointEdge h.2⟩
    simpa only [Prod.swap_swap] using hm.closure continuous_swap hd

private theorem low_first_face_mem_closure_prime {K : Coupling} (hK : K ∈ frontier lowDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = |Real.cos K.1.im|) :
    K ∈ closure (frontier lowDomain ∩ primeRegularJointEdges) := by
  obtain ⟨k,l,sgn,τ,a,hs,hτ,ha,he⟩ := low_first_face_parameter_exists hK hface
  obtain ⟨hx,hu,_,_⟩ := closure_low_bounds (frontier_subset_closure hK)
  have hv := nonnegative_realProduct_mem_closure_positive hx hu (realProduct_le_one_of_frontier_low hK)
  have hparam : ((K.1.re,K.2.re),a) ∈ closure (positiveRealSubcritical ×ˢ Ioo (-1:ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
    exact ⟨hv,abs_le.mp ha⟩
  have hm : MapsTo (lowFaceParameter k l sgn τ) (positiveRealSubcritical ×ˢ Ioo (-1:ℝ) 1)
      (closure (frontier lowDomain ∩ primeRegularJointEdges)) := by
    intro q hq
    exact regular_mem_closure_prime (Or.inr rfl)
      (lowFaceParameter_frontier k l hs hτ hq.1 (abs_lt.mpr hq.2))
      (lowFaceParameter_regular k l hs hτ hq.1 (abs_lt.mpr hq.2))
  have hh := hm.closure (lowFaceParameter_continuous k l sgn τ) hparam
  simpa only [closure_closure,he] using hh

/-- Selected prime phases are dense on every period of the actual low-temperature boundary. -/
theorem frontier_low_subset_closure_primeRegularJointEdges :
    frontier lowDomain ⊆ closure (frontier lowDomain ∩ primeRegularJointEdges) := by
  intro K hK
  rcases low_boundary_active_face hK with h | h
  · exact low_first_face_mem_closure_prime hK h
  · have hs := (swap_frontier_low_iff K).mpr hK
    have hf : faceRatio1 (K.swap.1.re,K.swap.2.re) = |Real.cos K.swap.1.im| := h
    have hd := low_first_face_mem_closure_prime hs hf
    have hm : MapsTo Prod.swap (frontier lowDomain ∩ primeRegularJointEdges)
        (frontier lowDomain ∩ primeRegularJointEdges) :=
      fun _ h => ⟨(swap_frontier_low_iff _).mpr h.1,swap_isPrimeRegularJointEdge h.2⟩
    simpa only [Prod.swap_swap] using hm.closure continuous_swap hd

end
end IsingBulk.Joint
