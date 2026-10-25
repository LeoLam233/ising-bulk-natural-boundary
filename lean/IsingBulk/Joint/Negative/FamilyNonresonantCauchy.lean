import IsingBulk.Joint.Negative.FamilyBoundaryGaps
import IsingBulk.Joint.Negative.FamilyGapCauchy
import IsingBulk.Joint.Negative.FamilyRestrictedJets
import IsingBulk.Joint.Negative.ModelData
import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterGaussian

/-! # Uniform physical nonresonant Cauchy bounds -/
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

theorem compact_actual_nonresonant_cauchy
    {b : ℝ} {Q : Set E} {p : ℕ} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q, S (curve (0,eta))≠0) (hamp : ∀eta∈Q, amp (0,eta)≠0)
    (he : ∀eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im)
    (hp : 2≤p) (hphase : IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (b:ℂ)) p) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀eta∈Q, ∀m j : ℕ, ¬p∣2*m+1 →
      ‖negativePaperParticleCoefficient (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) m j‖≤
        K*particleEdgeMajorant r C M (2*m+1)*(((2*m+1:ℕ):ℝ)/a)^j := by
  let H : ℂ × E→NumeratorParameter := fun q=>physicalNegativeParameter b (curve q) (amp q)
  have hH : ∀eta∈Q, AnalyticAt ℂ H (0,eta) := fun eta heta=>
    physicalNegativeParameter_analyticAt (hc eta heta) (ha eta heta) (hS eta heta) (hamp eta heta)
  have hcont : ContinuousOn (fun eta=>(H (0,eta)).2) Q := by
    intro eta heta
    exact ((hH eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).snd.continuousWithinAt
  obtain ⟨κ,hκ,hgap⟩ := compact_nonresonant_boundary_product_gap hb
    (hQ.image_of_continuousOn hcont) (by rintro v ⟨eta,heta,rfl⟩; exact hB eta heta)
    (by rintro v ⟨eta,heta,rfl⟩; exact div_ne_zero (hS eta heta) (hamp eta heta)) hp hphase
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hcb⟩ :=
    compact_family_integrand_cauchy_of_boundary_gap H hb hQ hH
      (fun eta heta=>physicalNegativeParameter_zero (hS eta heta) (he eta heta)) hB
      (fun eta heta=>div_ne_zero (hS eta heta) (hamp eta heta)) κ hκ
  refine ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta m j hm
  let n := 2*m
  have hn : Odd (n+1) := ⟨m,rfl⟩
  have hc' : AnalyticAt ℂ (fun t=>curve (t,eta)) 0 :=
    (hc eta heta).comp (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have ha' : AnalyticAt ℂ (fun t=>amp (t,eta)) 0 :=
    (ha eta heta).comp (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  unfold negativePaperParticleCoefficient
  rw [(weightedShiftedPhysicalDensity_boundary_integral n hn hc' ha' (hS eta heta)
    (he eta heta) hb (hB eta heta) j).2]
  apply physical_restricted_boundary_jet_bound n j hn hc' (hS eta heta) (he eta heta) hb (hB eta heta)
    measurableSet_Icc (fun _ hv=>hv)
    (mul_nonneg (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity))
  intro v _hv
  have hh := hcb eta heta j (n+1) (by omega) (negativeShiftedAngles n v)
    (fun i=>wrapAngle_mem _)
    (hgap (H (0,eta)).2 (mem_image_of_mem _ heta) (n+1) hm (negativeShiftedAngles n v)
      (fun i=>wrapAngle_mem _))
  rw [cauchy_gap_rearrange] at hh
  exact hh


/-- A fixed selected root phase gives a common Gaussian estimate for every
nonresonant odd coefficient across the entire compact family. -/
theorem compact_actual_nonresonant_gaussian
    {b : ℝ} {Q : Set E} {p : ℕ} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q, S (curve (0,eta))≠0) (hamp : ∀eta∈Q, amp (0,eta)≠0)
    (he : ∀eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im)
    (hp : 2≤p) (hphase : IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (b:ℂ)) p) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀eta∈Q, ∀m j : ℕ, ¬p∣2*m+1 →
      ‖negativePaperParticleCoefficient (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) m j‖≤
        gaussianEnvelope g D (2*m+1) j := by
  classical
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hcb⟩ :=
    compact_actual_nonresonant_cauchy curve amp hb hQ hc ha hS hamp he hB hp hphase
  obtain ⟨g,_Ds,L,_Q,hg,_hDs,hL,_hQ,hfamily⟩ :=
    selected_particle_coefficient_family_gaussian (K := K) (fun m : ℕ=>2*m+1)
      (by intro x y h; dsimp at h; omega) (fun m=>by omega) hr hr1 hC hM haR
  refine ⟨g,L,hg,hL,?_⟩
  intro eta heta m j hm
  let F : ℕ→ℕ→ℂ := fun m j=>if ¬p∣2*m+1 then
    negativePaperParticleCoefficient (fun t=>curve (t,eta)) (fun t=>amp (t,eta)) m j else 0
  have hF : ∀m j : ℕ, ‖F m j‖≤K*particleEdgeMajorant r C M (2*m+1)*(((2*m+1:ℕ):ℝ)/a)^j := by
    intro m j
    by_cases hm : p∣2*m+1
    · simp only [F,hm,not_true_eq_false,ite_false,norm_zero]
      exact mul_nonneg (mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (by positivity)
    · simpa only [F,hm,not_false_eq_true,ite_true] using hcb eta heta m j hm
  simpa only [F,hm,not_false_eq_true,ite_true,gaussianEnvelope,Nat.cast_add,Nat.cast_one] using (hfamily F hF).1 m j

end
end IsingBulk.Joint.Negative
