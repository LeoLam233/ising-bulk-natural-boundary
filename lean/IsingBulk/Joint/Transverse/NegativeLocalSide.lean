import IsingBulk.Joint.Transverse.LocalSide
import IsingBulk.Joint.RegularEdges.NegativeEvenIdentity

namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

def negativeFaceNeighborhood : Set Coupling :=
  {K | S K≠0 ∧ 0<(-transferB K).im ∧ |faceA K|<1 ∧ faceB K<1}

theorem negativeFaceNeighborhood_isOpen : IsOpen negativeFaceNeighborhood := by
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  have hC := (transferC_analyticAt hK.1).continuousAt
  have hB := (transferB_analyticAt hK.1).continuousAt
  have hbi : (transferB K).im≠0 := by
    have hh := hK.2.1
    simp only [Complex.neg_im] at hh
    linarith
  have hfB : ContinuousAt faceB K :=
    (Complex.continuous_im.continuousAt.comp hC).div
      (Complex.continuous_im.continuousAt.comp hB) hbi
  have hfA : ContinuousAt faceA K :=
    (Complex.continuous_re.continuousAt.comp hC).sub
      ((Complex.continuous_re.continuousAt.comp hB).mul hfB)
  filter_upwards [continuous_S.continuousAt.eventually_ne hK.1,
    (Complex.continuous_im.continuousAt.comp hB.neg).eventually_const_lt hK.2.1,
    hfA.abs.eventually_lt_const hK.2.2.1,hfB.eventually_lt_const hK.2.2.2] with L hs hb ha hc
  exact ⟨hs,hb,ha,hc⟩

theorem mem_negativeFaceNeighborhood {K : Coupling} {b : ℝ}
    (hS : S K≠0) (hB : 0<(-transferB K).im) (hb : |b|<1)
    (he : negativeParameter b K=0) : K∈negativeFaceNeighborhood := by
  have hbi : (transferB K).im≠0 := by simp only [Complex.neg_im] at hB; linarith
  have hc : transferC K=(b:ℂ)+transferB K*((-1:ℝ):ℂ) := by
    unfold negativeParameter at he
    push_cast
    linear_combination he
  have hf := transfer_face_coordinates_unique hbi hc
  exact ⟨hS,hB,by simpa [hf.1] using hb,by rw [hf.2]; norm_num⟩

theorem negativeFace_complement_iff {K : Coupling} (hK : K∈negativeFaceNeighborhood) (b : ℝ) :
    K∉spectralSet ↔ 0<(negativeParameter b K).im := by
  have hbi : (transferB K).im<0 := by simpa only [Complex.neg_im,neg_pos] using hK.2.1
  rw [spectralSet_iff_face_coordinates hK.1 hbi.ne]
  have ha : faceA K∈Icc (-1:ℝ) 1 := ⟨(abs_lt.mp hK.2.2.1).1.le,(abs_lt.mp hK.2.2.1).2.le⟩
  have he : (negativeParameter b K).im=(transferB K).im*(faceB K+1) := by
    simp only [negativeParameter,Complex.sub_im,Complex.add_im,Complex.ofReal_im,sub_zero,faceB]
    rw [mul_add,mul_div_cancel₀ _ hbi.ne,mul_one]
  rw [and_iff_right ha,mem_Icc,and_iff_left hK.2.2.2.le,not_le,he]
  constructor
  · intro hb
    exact mul_pos_of_neg_of_neg hbi (by linarith)
  · intro hp
    by_contra hn
    push Not at hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hbi.le (by linarith))) hp

theorem negativeFace_domain_side {D : Set Coupling} {K : Coupling} {b : ℝ}
    (hclosure : K∈closure D) (hDsub : D⊆spectralSetᶜ)
    (hcomp : ∀ a∈D, connectedComponentIn spectralSetᶜ a=D)
    (hS : S K≠0) (hp : p K^2≠1) (hB : 0<(-transferB K).im)
    (hb : |b|<1) (he : negativeParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆negativeFaceNeighborhood ∧
      ∀ L∈U, L∈D ↔ 0<(negativeParameter b L).im := by
  obtain ⟨e,hKs,hef,_,_⟩ := exists_transfer_localAnalyticEquiv hS hp
  have hKface := mem_negativeFaceNeighborhood hS hB hb he
  have hV : IsOpen (e.target ∩ e.symm ⁻¹' negativeFaceNeighborhood) :=
    e.isOpen_inter_preimage_symm negativeFaceNeighborhood_isOpen
  have hKV : e K∈e.target ∩ e.symm ⁻¹' negativeFaceNeighborhood :=
    ⟨e.map_source hKs,by simpa [e.left_inv hKs] using hKface⟩
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hKV)
  let U := e.source ∩ e ⁻¹' ball (e K) r
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hKU : K∈U := ⟨hKs,mem_ball_self hr⟩
  have hUface : U⊆negativeFaceNeighborhood := by
    intro L hL
    have hh := (hrV hL.2).2
    simpa [e.left_inv hL.1] using hh
  let H : Set Coupling := ball (e K) r ∩ {q | 0<(q.1+q.2).im}
  have hlin : IsLinearMap ℝ (fun q : Coupling => (q.1+q.2).im) := by
    constructor
    · intro x y
      simp only [Prod.fst_add,Prod.snd_add,Complex.add_im]
      ring
    · intro a x
      simp only [Prod.smul_fst,Prod.smul_snd,Complex.add_im,Complex.smul_im,smul_eq_mul]
      ring
  have hH : IsPreconnected H := ((convex_ball (e K) r).inter
    (convex_halfSpace_gt hlin 0)).isPreconnected
  have hHt : H⊆e.target := fun _ hq => (hrV hq.1).1
  have hHC : IsPreconnected (e.symm '' H) := hH.image e.symm (e.symm.continuousOn.mono hHt)
  have hHspec : e.symm '' H⊆spectralSetᶜ := by
    rintro L ⟨q,hq,rfl⟩
    apply (negativeFace_complement_iff (hrV hq.1).2 b).mpr
    have hqeq : transferChart (e.symm q)=q := by rw [←hef]; exact e.right_inv (hHt hq)
    change 0<(transferC (e.symm q)+transferB (e.symm q)-(b:ℂ)).im
    have hc := congrArg Prod.fst hqeq
    have hd := congrArg Prod.snd hqeq
    change transferC (e.symm q)=q.1 at hc
    change transferB (e.symm q)=q.2 at hd
    simpa [hc,hd] using hq.2
  obtain ⟨a,haU,haD⟩ := mem_closure_iff.mp hclosure U hU hKU
  have haH : a∈e.symm '' H := by
    refine ⟨e a,⟨haU.2,?_⟩,e.left_inv haU.1⟩
    have hh := (negativeFace_complement_iff (hUface haU) b).mp (hDsub haD)
    simpa [hef,transferChart,negativeParameter] using hh
  have hHD : e.symm '' H⊆D := by
    rw [←hcomp a haD]
    exact hHC.subset_connectedComponentIn haH hHspec
  refine ⟨U,hU,hKU,hUface,?_⟩
  intro L hL
  constructor
  · intro hLD
    exact (negativeFace_complement_iff (hUface hL) b).mp (hDsub hLD)
  · intro hLi
    apply hHD
    refine ⟨e L,⟨hL.2,?_⟩,e.left_inv hL.1⟩
    simpa [hef,transferChart,negativeParameter] using hLi

theorem negativeFace_high_side {K : Coupling} {b : ℝ}
    (hK : K∈frontier highDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(-transferB K).im) (hb : |b|<1) (he : negativeParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆negativeFaceNeighborhood ∧
      ∀ L∈U, L∈highDomain ↔ 0<(negativeParameter b L).im :=
  negativeFace_domain_side hK.1 highDomain_subset_spectralComplement highDomain_component hS hp hB hb he

theorem negativeFace_low_side {K : Coupling} {b : ℝ}
    (hK : K∈frontier lowDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(-transferB K).im) (hb : |b|<1) (he : negativeParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆negativeFaceNeighborhood ∧
      ∀ L∈U, L∈lowDomain ↔ 0<(negativeParameter b L).im :=
  negativeFace_domain_side hK.1 lowDomain_subset_spectralComplement lowDomain_component hS hp hB hb he

end
end IsingBulk.Joint.Transverse
