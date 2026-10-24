import IsingBulk.Anisotropic.RegularEdges.FullIntegrandBound
import IsingBulk.Anisotropic.RegularEdges.UpperSingularJets
import IsingBulk.Anisotropic.RegularEdges.ParticleMajorant

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

/-- Actual differentiated full angular integrands, uniformly in every particle
number and every retained coordinate selection. All constants precede N. -/
theorem edgeFullIntegrand_uniform_jets_upper {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ v : ℂ, 0<v.im → ‖v‖<δ → ∀ (N m : ℕ) [Nonempty (Fin m)]
        (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → (fun i => q (p i))≠0 →
      ‖iteratedDeriv j (fun u => edgeFullIntegrand b B S u q) v‖≤
        D*particleEdgeMajorant r C M N*(N:ℝ)^j*
          (1+‖fun i => q (p i)‖^(-(2*(j+1):ℝ))) := by
  obtain ⟨δ,r,C,M,K,hδ,hr,hr1,hC,hM,hK,hnum⟩ := edgeNumerator_all_jets hb hB hc hS hS0 j
  obtain ⟨η,A,hη,hA,hrec⟩ := edgeReciprocal_retained_jets_up_to_upper hb hB hc j
  obtain ⟨τ,hτ,hτball⟩ := Metric.mem_nhds_iff.mp (edgeReciprocal_eventually_analytic hb hB hc)
  let D : ℝ := 2^(j+1)*K*A+K
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨min δ (min η τ),r,C,M,D,lt_min hδ (lt_min hη hτ),hr,hr1,hC,hM,hD,?_⟩
  intro v hε he N m _ q p hq hq0
  have heδ : ‖v‖<δ := he.trans_le (min_le_left _ _)
  have heη : ‖v‖<η := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heτ : ‖v‖<τ := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have him : 0<v.im := hε
  have hN : 0<N := Nat.zero_lt_of_lt (p (Classical.arbitrary (Fin m))).isLt
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hNp : 1≤(N:ℝ)^j := one_le_pow₀ hNr
  have hn := hnum v heδ N q hq
  have hg := hτball (show v∈ball (0:ℂ) τ by simpa using heτ) him N hN q hq
  have hgj := hrec v hε heη N m q p hq hq0
  let E := particleEdgeMajorant r C M N
  let P := ‖fun i => q (p i)‖^(-(2*(j+1):ℝ))
  have hE : 0≤E := particleEdgeMajorant_nonneg hr.le hC.le hM.le N
  have hP : 0≤P := Real.rpow_nonneg (norm_nonneg _) _
  have hh := analytic_affine_product_jet_bound
    (fun u => edgeNumerator b B S u (List.ofFn q))
    (fun u => (1-edgeRootProduct b B u q)⁻¹) v j hn.1 hg
    (mul_nonneg hK.le hE) (show 0≤A*(N:ℝ)^j*P by positivity) hn.2 hgj
  change ‖iteratedDeriv j (fun u => edgeFullIntegrand b B S u q) v‖≤_ at hh
  apply hh.trans
  change 2^(j+1)*(K*E)*(A*(N:ℝ)^j*P)+K*E ≤ D*E*(N:ℝ)^j*(1+P)
  have hKE : 0≤K*E := mul_nonneg hK.le hE
  have h₁ : K*E≤K*E*(N:ℝ)^j := le_mul_of_one_le_right hKE hNp
  have h₂ : 0≤2^(j+1)*K*A*E*(N:ℝ)^j := by positivity
  have h₃ : 0≤K*E*(N:ℝ)^j*P := by positivity
  dsimp [D]
  nlinarith

end IsingBulk.Anisotropic.RegularEdges
