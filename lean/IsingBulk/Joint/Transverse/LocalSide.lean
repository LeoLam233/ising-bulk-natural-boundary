import IsingBulk.Joint.Transverse.TransferFace
import IsingBulk.Joint.Geometry.Components
import Mathlib.Analysis.Complex.Convex

/-! # Actual physical domain side at a regular face
A local analytic chart and a convex half-ball identify the genuine connected
component of the spectral complement, rather than merely naming a side.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

theorem positiveFace_domain_side {D : Set Coupling} {K : Coupling} {b : ℝ}
    (hclosure : K∈closure D) (hDsub : D⊆spectralSetᶜ)
    (hcomp : ∀ a∈D, connectedComponentIn spectralSetᶜ a=D)
    (hS : S K≠0) (hp : p K^2≠1) (hB : 0<(transferB K).im)
    (hb : |b|<1) (he : positiveParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆positiveFaceNeighborhood ∧
      ∀ L∈U, L∈D ↔ 0<(positiveParameter b L).im := by
  obtain ⟨e,hKs,hef,_,_⟩ := exists_transfer_localAnalyticEquiv hS hp
  have hKface := mem_positiveFaceNeighborhood hS hB hb he
  have hV : IsOpen (e.target ∩ e.symm ⁻¹' positiveFaceNeighborhood) :=
    e.isOpen_inter_preimage_symm positiveFaceNeighborhood_isOpen
  have hKV : e K∈e.target ∩ e.symm ⁻¹' positiveFaceNeighborhood :=
    ⟨e.map_source hKs,by simpa [e.left_inv hKs] using hKface⟩
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hKV)
  let U := e.source ∩ e ⁻¹' ball (e K) r
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hKU : K∈U := ⟨hKs,mem_ball_self hr⟩
  have hUface : U⊆positiveFaceNeighborhood := by
    intro L hL
    have hh := (hrV hL.2).2
    simpa [e.left_inv hL.1] using hh
  let H : Set Coupling := ball (e K) r ∩ {q | 0<(q.1-q.2).im}
  have hlin : IsLinearMap ℝ (fun q : Coupling => (q.1-q.2).im) := by
    constructor
    · intro x y
      simp only [Prod.fst_add,Prod.snd_add,Complex.sub_im,Complex.add_im]
      ring
    · intro a x
      simp only [Prod.smul_fst,Prod.smul_snd,Complex.sub_im,Complex.smul_im,smul_eq_mul]
      ring
  have hH : IsPreconnected H := ((convex_ball (e K) r).inter
    (convex_halfSpace_gt hlin 0)).isPreconnected
  have hHt : H⊆e.target := fun _ hq => (hrV hq.1).1
  have hHC : IsPreconnected (e.symm '' H) := hH.image e.symm (e.symm.continuousOn.mono hHt)
  have hHspec : e.symm '' H⊆spectralSetᶜ := by
    rintro L ⟨q,hq,rfl⟩
    apply (positiveFace_complement_iff (hrV hq.1).2 b).mpr
    have hqeq : transferChart (e.symm q)=q := by rw [←hef]; exact e.right_inv (hHt hq)
    change 0<(transferC (e.symm q)-transferB (e.symm q)-(b:ℂ)).im
    have hc := congrArg Prod.fst hqeq
    have hd := congrArg Prod.snd hqeq
    change transferC (e.symm q)=q.1 at hc
    change transferB (e.symm q)=q.2 at hd
    simpa [hc,hd] using hq.2
  obtain ⟨a,haU,haD⟩ := mem_closure_iff.mp hclosure U hU hKU
  have haH : a∈e.symm '' H := by
    refine ⟨e a,⟨haU.2,?_⟩,e.left_inv haU.1⟩
    have hh := (positiveFace_complement_iff (hUface haU) b).mp (hDsub haD)
    simpa [hef,transferChart,positiveParameter] using hh
  have hHD : e.symm '' H⊆D := by
    rw [←hcomp a haD]
    exact hHC.subset_connectedComponentIn haH hHspec
  refine ⟨U,hU,hKU,hUface,?_⟩
  intro L hL
  constructor
  · intro hLD
    exact (positiveFace_complement_iff (hUface hL) b).mp (hDsub hLD)
  · intro hLi
    apply hHD
    refine ⟨e L,⟨hL.2,?_⟩,e.left_inv hL.1⟩
    simpa [hef,transferChart,positiveParameter] using hLi

theorem positiveFace_high_side {K : Coupling} {b : ℝ}
    (hK : K∈frontier highDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(transferB K).im) (hb : |b|<1) (he : positiveParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆positiveFaceNeighborhood ∧
      ∀ L∈U, L∈highDomain ↔ 0<(positiveParameter b L).im :=
  positiveFace_domain_side hK.1 highDomain_subset_spectralComplement highDomain_component hS hp hB hb he

theorem positiveFace_low_side {K : Coupling} {b : ℝ}
    (hK : K∈frontier lowDomain) (hS : S K≠0) (hp : p K^2≠1)
    (hB : 0<(transferB K).im) (hb : |b|<1) (he : positiveParameter b K=0) :
    ∃ U : Set Coupling, IsOpen U ∧ K∈U ∧ U⊆positiveFaceNeighborhood ∧
      ∀ L∈U, L∈lowDomain ↔ 0<(positiveParameter b L).im :=
  positiveFace_domain_side hK.1 lowDomain_subset_spectralComplement lowDomain_component hS hp hB hb he

end
end IsingBulk.Joint.Transverse
