import IsingBulk.Joint.Negative.FamilyBoundaryGaps
import IsingBulk.Joint.Negative.FamilyGapCauchy
import IsingBulk.Joint.Negative.FamilyRestrictedJets
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterGaussian

/-! # Uniform physical outer and nonresonant Cauchy bounds -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Anisotropic.NegativeCycles IsingBulk.Joint.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem cauchy_gap_rearrange (j : ℕ) (a N K : ℝ) :
    (j.factorial:ℝ)*K/(a/N)^j=(j.factorial:ℝ)*(K*(N/a)^j) := by
  simp only [div_eq_mul_inv,mul_pow,mul_inv_rev,inv_pow,inv_inv]
  ring

/-- Common physical outer estimates at every odd particle order, with actual
varying anisotropy and particle weight. The complete angular resolvent remains
inside the proof, and no inward-path or derivative-exchange premise is used. -/
theorem compact_actual_outer_cauchy
    {b : ℝ} {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q, S (curve (0,eta))≠0) (hamp : ∀eta∈Q, amp (0,eta)≠0)
    (he : ∀eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀eta∈Q, ∀n j : ℕ,Odd (n+1) →
      ‖∫v in physicalOuterRegion n σ,
        physicalDensityTaylor n (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) j v‖≤
        K*particleEdgeMajorant r C M (n+1)*(((n+1:ℕ):ℝ)/a)^j := by
  let H : ℂ × E→NumeratorParameter := fun q=>physicalNegativeParameter b (curve q) (amp q)
  have hH : ∀eta∈Q, AnalyticAt ℂ H (0,eta) := fun eta heta=>
    physicalNegativeParameter_analyticAt (hc eta heta) (ha eta heta) (hS eta heta) (hamp eta heta)
  have hcont : ContinuousOn (fun eta=>(H (0,eta)).2) Q := by
    intro eta heta
    exact ((hH eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).snd.continuousWithinAt
  obtain ⟨κ,hκ,hgap⟩ := compact_outer_boundary_product_gap hb
    (hQ.image_of_continuousOn hcont) (by rintro v ⟨eta,heta,rfl⟩; exact hB eta heta) σ hσ
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hcb⟩ :=
    compact_family_integrand_cauchy_of_boundary_gap H hb hQ hH
      (fun eta heta=>physicalNegativeParameter_zero (hS eta heta) (he eta heta)) hB
      (fun eta heta=>div_ne_zero (hS eta heta) (hamp eta heta)) κ hκ
  refine ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta n j hn
  have hc' : AnalyticAt ℂ (fun t=>curve (t,eta)) 0 :=
    (hc eta heta).comp (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  apply physical_restricted_boundary_jet_bound n j hn hc' (hS eta heta) (he eta heta) hb (hB eta heta)
    (measurableSet_Icc.inter (measurableSet_le measurable_const (physicalShiftedEnergy_measurable n)))
    (fun _ hv=>hv.1)
    (mul_nonneg (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity))
  intro v hv
  have hh := hcb eta heta j (n+1) (by omega) (negativeShiftedAngles n v)
    (fun i=>wrapAngle_mem _)
    (hgap (H (0,eta)).2 (mem_image_of_mem _ heta) (n+1) (negativeShiftedAngles n v)
      (fun i=>wrapAngle_mem _) hv.2)
  rw [cauchy_gap_rearrange] at hh
  exact hh

/-- The resulting outer Gaussian constants precede the family member and every
particle and derivative order. -/
theorem compact_actual_outer_gaussian
    {b : ℝ} {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q, S (curve (0,eta))≠0) (hamp : ∀eta∈Q, amp (0,eta)≠0)
    (he : ∀eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im)
    (σ : ℝ) (hσ : 0<σ) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀eta∈Q, ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) σ,
        physicalDensityTaylor (2*m) (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) j v‖≤
        gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,_hK,hcb⟩ :=
    compact_actual_outer_cauchy curve amp hb hQ hc ha hS hamp he hB σ hσ
  obtain ⟨g,_Ds,L,_Q,hg,_hDs,hL,_hQ,hfamily⟩ :=
    selected_particle_coefficient_family_gaussian (K := K) (fun m : ℕ=>2*m+1)
      (by intro x y h; dsimp at h; omega) (fun m=>by omega) hr hr1 hC hM haR
  refine ⟨g,L,hg,hL,?_⟩
  intro eta heta m j
  exact (hfamily (fun m j=>∫v in physicalOuterRegion (2*m) σ,
    physicalDensityTaylor (2*m) (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) j v)
    (fun m j=>hcb eta heta (2*m) j ⟨m,by omega⟩)).1 m j

end
end IsingBulk.Joint.Negative
