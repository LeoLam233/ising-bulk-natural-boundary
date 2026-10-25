import IsingBulk.Joint.Geometry.PrimeRegular
import IsingBulk.Joint.Geometry.FlatFaceBoundary

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology
open IsingBulk.Anisotropic Transverse

/-- Selected points on one exact transfer edge, with the anisotropy held fixed.
Every point remains on the same physical frontier, with the same endpoint. -/
def selectedTransferFace (D : Set Coupling) (B₀ : ℂ) (eps : ℝ) : Set Coupling :=
  {L | L∈frontier D ∧ IsPrimeRegularJointEdge L ∧ transferB L=B₀ ∧
    ∃b : ℝ, |b|<1 ∧ b∈primePhaseCosines ∧
      transferC L=(b:ℂ)+(eps:ℂ)*B₀}

private theorem physical_domain_side {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} {b eps : ℝ} (hK : K ∈ frontier D)
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1)
    (heps : eps = -1 ∨ eps = 1) (hB : 0 < eps*(transferB K).im)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) :
    ∃ U : Set Coupling, IsOpen U ∧ K ∈ U ∧
      ∀ L ∈ U, L ∈ D ↔ 0 < flatNormal eps (transferChart L) := by
  have hs : D ⊆ spectralSetᶜ := by rcases hD with rfl | rfl; exact highDomain_subset_spectralComplement; exact lowDomain_subset_spectralComplement
  have hc : ∀ a ∈ D, connectedComponentIn spectralSetᶜ a = D := by
    rcases hD with rfl | rfl; exact highDomain_component; exact lowDomain_component
  rcases heps with heps | heps
  · have hBi : 0 < (-transferB K).im := by simpa [heps] using hB
    have hz : negativeParameter b K = 0 := by
      simp only [heps,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] at he
      dsimp [negativeParameter]
      linear_combination he
    obtain ⟨U,hU,hKU,_,hside⟩ := negativeFace_domain_side hK.1 hs hc hS hp hBi hb hz
    refine ⟨U,hU,hKU,?_⟩
    intro L hL
    simpa [flatNormal,transferChart,negativeParameter,heps] using hside L hL
  · have hBi : 0 < (transferB K).im := by simpa [heps] using hB
    have hz : positiveParameter b K = 0 := by
      simp only [heps,Complex.ofReal_one,one_mul] at he
      dsimp [positiveParameter]
      linear_combination he
    obtain ⟨U,hU,hKU,_,hside⟩ := positiveFace_domain_side hK.1 hs hc hS hp hBi hb hz
    refine ⟨U,hU,hKU,?_⟩
    intro L hL
    simpa [flatNormal,transferChart,positiveParameter,heps] using hside L hL

/-- Vary the free real coordinate in a genuine local analytic (C,B) chart,
keeping B fixed. Prime phases are dense on this actual boundary slice. -/
theorem oriented_face_mem_closure_prime_fixed_B {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} {b eps : ℝ} (hK : K ∈ frontier D)
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1)
    (heps : eps = -1 ∨ eps = 1) (hB : 0 < eps*(transferB K).im)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) :
    K ∈ closure (selectedTransferFace D (transferB K) eps) := by
  have ho : IsOpen D := by rcases hD with rfl | rfl; exact highDomain_isOpen; exact lowDomain_isOpen
  have hfront : frontier D ⊆ frontier highDomain ∪ frontier lowDomain := by
    rcases hD with rfl | rfl; exact subset_union_left; exact subset_union_right
  have hBne : (transferB K).im ≠ 0 := by intro hn; rw [hn,mul_zero] at hB; exact lt_irrefl _ hB
  obtain ⟨U,hU,hKU,hside⟩ := physical_domain_side hD hK hS hp hb heps hB he
  obtain ⟨e,hKs,hef,_,_⟩ := exists_transfer_localAnalyticEquiv hS hp
  let q : ℝ → Coupling := fun t => ((t:ℂ)+(eps:ℂ)*transferB K,transferB K)
  let g : ℝ → Coupling := fun t => e.symm (q t)
  have hqb : q b = e K := by rw [hef]; exact Prod.ext he.symm rfl
  have hq : Continuous q := by unfold q; fun_prop
  have hg : Tendsto g (𝓝 b) (𝓝 K) := by
    apply (e.tendsto_symm hKs).comp
    rw [←hqb]
    exact hq.continuousAt
  have hqt : ∀ᶠ t : ℝ in 𝓝 b, q t ∈ e.target :=
    hq.continuousAt.preimage_mem_nhds (by rw [hqb]; exact e.open_target.mem_nhds (e.map_source hKs))
  have hgu : ∀ᶠ t : ℝ in 𝓝 b, g t ∈ U := hg (hU.mem_nhds hKU)
  have hgs : ∀ᶠ t : ℝ in 𝓝 b, S (g t) ≠ 0 := hg.eventually (continuous_S.continuousAt.eventually_ne hS)
  have hgp : ∀ᶠ t : ℝ in 𝓝 b, p (g t)^2 ≠ 1 := hg.eventually ((continuous_p.pow 2).continuousAt.eventually_ne hp)
  have hti : ∀ᶠ t : ℝ in 𝓝 b, |t| < 1 := continuousAt_id.abs.eventually_lt_const hb
  have hgood : ∀ᶠ t : ℝ in 𝓝 b, g t ∈ frontier D ∧
      (t ∈ primePhaseCosines → g t ∈ selectedTransferFace D (transferB K) eps) := by
    filter_upwards [hqt,hgu,hgs,hgp,hti] with t ht hu hs hpp htb
    have hEq : transferChart (g t) = q t := by rw [←hef]; exact e.right_inv ht
    have hC : transferC (g t) = (t:ℂ)+(eps:ℂ)*transferB K := congrArg Prod.fst hEq
    have hBB : transferB (g t) = transferB K := congrArg Prod.snd hEq
    have hgn : flatNormal eps (e (g t)) = 0 := by rw [hef,hEq]; simp [flatNormal,q]
    have hgf : g t ∈ frontier D := frontier_of_flat_chart ho hU e
      (fun L hL => by simpa [hef] using hside L hL) (e.map_target ht) hu hgn
    refine ⟨hgf,?_⟩
    intro hprime
    have hct : transferC (g t) = (t:ℂ)+(eps:ℂ)*transferB (g t) := by rw [hC,hBB]
    exact ⟨hgf,primeRegularJointEdge_of_transfer
      (regularJointEdge_of_transfer (hfront hgf) hs (by rw [hBB]; exact hBne) hpp htb heps hct)
      htb hprime heps hct,hBB,t,htb,hprime,hC⟩
  have hbD := interior_subset_closure_primePhaseCosines (abs_lt.mp hb)
  apply mem_closure_iff_nhds.mpr
  intro N hN
  obtain ⟨t,ht,hprime⟩ := mem_closure_iff_nhds.mp hbD _ (inter_mem (hg hN) hgood)
  exact ⟨g t,ht.1,ht.2.2 hprime⟩

/-- The original global closure interface follows from the stronger exact
same-face, fixed-anisotropy statement. -/
theorem oriented_face_mem_closure_prime {D : Set Coupling} (hD : D = highDomain ∨ D = lowDomain)
    {K : Coupling} {b eps : ℝ} (hK : K ∈ frontier D)
    (hS : S K ≠ 0) (hp : p K^2 ≠ 1) (hb : |b| < 1)
    (heps : eps = -1 ∨ eps = 1) (hB : 0 < eps*(transferB K).im)
    (he : transferC K = (b:ℂ)+(eps:ℂ)*transferB K) :
    K ∈ closure (frontier D ∩ primeRegularJointEdges) :=
  closure_mono (show selectedTransferFace D (transferB K) eps ⊆
      frontier D ∩ primeRegularJointEdges from fun _ h=>⟨h.1,h.2.1⟩)
    (oriented_face_mem_closure_prime_fixed_B hD hK hS hp hb heps hB he)

end
end IsingBulk.Joint
