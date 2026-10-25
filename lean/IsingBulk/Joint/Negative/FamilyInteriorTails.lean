import IsingBulk.Joint.Negative.IndependentCoefficientJets
import IsingBulk.Joint.Negative.FamilyAnalyticControl
import IsingBulk.Joint.RegularEdges.FamilyTailJets

/-! # Common interior derivative tails after the actual nonconstant family map -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Joint.RegularEdges IsingBulk.Joint.FormFactors Set Filter Metric
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_parametric_negative_coefficient_tails {b : ℝ}
    (H : ℂ × E→NumeratorParameter) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hH : ∀eta∈Q, AnalyticAt ℂ H (0,eta))
    (hzero : ∀eta∈Q,(H (0,eta)).1=0)
    (hB : ∀eta∈Q,0<(H (0,eta)).2.1.im) (hS : ∀eta∈Q,(H (0,eta)).2.2≠0) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ, ∃G : ℕ→ℝ, Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q, ∀u : ℂ, ‖u‖<δ → 0<(H (u,eta)).1.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>independentNegativeCoefficient (2*j+3+k) b (H (t,eta))) u‖≤G k := by
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ H q ∧ 0<(H q).2.1.im ∧ (H q).2.2≠0}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      ((continuousAt_const.eventually_lt
        (Complex.continuous_im.continuousAt.comp (hq.1.continuousAt.snd.fst)) hq.2.1).and
        (hq.1.continuousAt.snd.snd.eventually_ne hq.2.2))
  obtain ⟨r,hr,ht⟩ := compact_product_tube hQ hU
    (fun eta heta=>⟨hH eta heta,hB eta heta,hS eta heta⟩)
  let ρ := r/2
  have hρ : 0<ρ := half_pos hr
  have htube : ∀eta∈Q,∀u : ℂ,‖u‖≤ρ → (u,eta)∈U :=
    fun eta heta u hu=>ht eta heta u (hu.trans_lt (half_lt_self hr))
  let T : Set (ℂ × E) := closedBall 0 ρ ×ˢ Q
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hQ
  have hc : ContinuousOn (fun q=>(H q).2) T := by
    intro q hq
    exact (htube q.2 hq.2 q.1 (by simpa using hq.1)).1.continuousAt.snd.continuousWithinAt
  let K := (fun q=>(H q).2) '' T
  have hK : IsCompact K := hT.image_of_continuousOn hc
  have hKB : ∀v∈K,0<v.1.im := by
    rintro v ⟨q,hq,rfl⟩
    exact (htube q.2 hq.2 q.1 (by simpa using hq.1)).2.1
  have hKS : ∀v∈K,v.2≠0 := by
    rintro v ⟨q,hq,rfl⟩
    exact (htube q.2 hq.2 q.1 (by simpa using hq.1)).2.2
  obtain ⟨ε,hε,hjets⟩ := compact_negative_coefficient_summable_mixed_jets hb hK hKB hKS
  obtain ⟨κ,L,hκ,hL,hlin⟩ := compact_family_analytic_linear_bound (fun q=>(H q).1) hQ
    (fun eta heta=>analyticAt_fst.comp (hH eta heta))
  choose M hM hM0 hMb using hjets
  refine ⟨min (ρ/2) (min κ (ε/L)),lt_min (half_pos hρ) (lt_min hκ (div_pos hε hL)),?_⟩
  intro j
  obtain ⟨D,hD,hDj⟩ := compact_family_trace_geometric_jets H hQ hρ
    (fun eta heta u hu=>(htube eta heta u hu).1) j
  let W : ℕ→ℝ := fun k=>∑i∈Finset.range (j+1),M i (2*(j-i)+k)
  have hW (k : ℕ) : 0≤W k := Finset.sum_nonneg (fun i _=>hM0 i _)
  have hWs : Summable W := by
    apply summable_sum
    intro i _
    exact (hM i).comp_injective (i := fun k : ℕ=>2*(j-i)+k) (by intro a c h; dsimp at h; omega)
  refine ⟨fun k=>(j.factorial:ℝ)*D^j*W k,hWs.mul_left _,fun k=>mul_nonneg (by positivity) (hW k),?_⟩
  intro eta heta u hu hi k
  have huρ : ‖u‖<ρ/2 := hu.trans_le (min_le_left _ _)
  have huρ' : ‖u‖≤ρ := (huρ.trans (half_lt_self hρ)).le
  have hHp : H (u,eta)∈independentUpperDomain :=
    ⟨hi,(htube eta heta u huρ').2⟩
  have hHu : H (u,eta)∈ball (0,(H (u,eta)).2) ε := by
    simp only [mem_ball,Prod.dist_eq,dist_zero_right,dist_self,max_lt_iff]
    refine ⟨?_,hε⟩
    have huκ : ‖u‖<κ := (hu.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hh := (hlin eta heta u huκ).2
    rw [hzero eta heta,sub_zero] at hh
    have hl : ‖u‖*L<ε := (lt_div_iff₀ hL).mp ((hu.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    exact hh.trans_lt (by simpa only [mul_comm] using hl)
  have houter : ∀i≤j, ‖iteratedFDeriv ℂ i (independentNegativeCoefficient (2*j+3+k) b) (H (u,eta))‖≤W k := by
    intro i hij
    have hh := hMb i (H (u,eta)).2 ⟨(u,eta),⟨by simpa using huρ',heta⟩,rfl⟩
      (H (u,eta)) hHu hi (2*(j-i)+k)
    rw [show 2*i+3+(2*(j-i)+k)=2*j+3+k by omega] at hh
    exact hh.trans (Finset.single_le_sum (f := fun a=>M a (2*(j-a)+k)) (fun a (_ : a∈Finset.range (j+1))=>hM0 a _)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega)))
  have htrace : AnalyticAt ℂ (fun t=>H (t,eta)) u :=
    (htube eta heta u huρ').1.comp (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hh := contDiffAt_composition_geometric_jets (f := fun t : ℂ=>H (t,eta)) j
    (independentNegativeCoefficient_contDiffAt _ j hHp) htrace.contDiffAt houter
    (hDj eta heta u huρ)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  simpa only [Function.comp_def,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Actual particle-weighted full coefficients on one common inward tube.
The only side condition is the genuine upper transfer-coordinate inequality,
which the normalized negative inward ray satisfies. -/
theorem compact_actual_negative_interior_tails {b : ℝ}
    (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,IsingBulk.Joint.S (curve (0,eta))≠0) (hamp : ∀eta∈Q,amp (0,eta)≠0)
    (he : ∀eta∈Q,A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*IsingBulk.Joint.S (curve (0,eta)))
    (hB : ∀eta∈Q,0<(-T (curve (0,eta))/IsingBulk.Joint.S (curve (0,eta))).im) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ →
        0<(transferC (curve (u,eta))+transferB (curve (u,eta))-(b:ℂ)).im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>amp (t,eta)^(2*j+3+k+1)*
        continuedAngularCoefficient (2*j+3+k) (curve (t,eta))) u‖≤G k := by
  let H : ℂ × E→NumeratorParameter := fun q=>physicalNegativeParameter b (curve q) (amp q)
  have hH : ∀eta∈Q,AnalyticAt ℂ H (0,eta) := fun eta heta=>
    physicalNegativeParameter_analyticAt (hc eta heta) (ha eta heta) (hS eta heta) (hamp eta heta)
  have hHS : ∀eta∈Q,(H (0,eta)).2.2≠0 := fun eta heta=>div_ne_zero (hS eta heta) (hamp eta heta)
  obtain ⟨δ,hδ,hjets⟩ := compact_parametric_negative_coefficient_tails H hb hQ hH
    (fun eta heta=>physicalNegativeParameter_zero (hS eta heta) (he eta heta)) hB hHS
  obtain ⟨ρ,hρ,htube⟩ := compact_admissible_family_tube
    (fun q=>(H q).2.1) (fun q=>(H q).2.2) hQ
    (fun eta heta=>analyticAt_fst.comp (analyticAt_snd.comp (hH eta heta)))
    (fun eta heta=>analyticAt_snd.comp (analyticAt_snd.comp (hH eta heta))) hB hHS
  obtain ⟨κ,L,hκ,_,hlin⟩ := compact_family_analytic_linear_bound H hQ hH
  refine ⟨min δ (min ρ κ),lt_min hδ (lt_min hρ hκ),?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hjets j
  refine ⟨G,hG,hG0,?_⟩
  intro eta heta u hu hi k
  have huδ := hu.trans_le (min_le_left _ _)
  have huρ := (hu.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have huκ := (hu.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hHp : H (u,eta)∈independentUpperDomain := ⟨hi,(htube eta heta u huρ.le).2.2⟩
  have heq : (fun t=>independentNegativeCoefficient (2*j+3+k) b (H (t,eta))) =ᶠ[𝓝 u]
      (fun t=>amp (t,eta)^(2*j+3+k+1)*continuedAngularCoefficient (2*j+3+k) (curve (t,eta))) := by
    filter_upwards [(hlin eta heta u huκ).1.continuousAt.preimage_mem_nhds
      (independentUpperDomain_isOpen.mem_nhds hHp)] with t ht
    exact independentNegativeCoefficient_eq_weighted_continued _ ht
  rw [←heq.iteratedDeriv_eq j]
  exact hbound eta heta u huδ hi k

end
end IsingBulk.Joint.Negative
