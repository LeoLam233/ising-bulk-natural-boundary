import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets
import IsingBulk.Joint.FormFactors.CompositionJets
import IsingBulk.Joint.Negative.CompactFamilies

/-! # Complete differentiated tails on arbitrary compact holomorphic families -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Joint.FormFactors
  IsingBulk.Joint.Negative Set Filter Metric
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_admissible_family_tube (B S : ℂ × E→ℂ) {Q : Set E}
    (hQ : IsCompact Q) (hBa : ∀eta∈Q, AnalyticAt ℂ B (0,eta))
    (hSa : ∀eta∈Q, AnalyticAt ℂ S (0,eta))
    (hB : ∀eta∈Q, 0<(B (0,eta)).im) (hS : ∀eta∈Q, S (0,eta)≠0) :
    ∃ρ : ℝ,0<ρ ∧ ∀eta∈Q, ∀u : ℂ, ‖u‖≤ρ →
      AnalyticAt ℂ B (u,eta) ∧ AnalyticAt ℂ S (u,eta) ∧ 0<(B (u,eta)).im ∧ S (u,eta)≠0 := by
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ B q ∧ AnalyticAt ℂ S q ∧ 0<(B q).im ∧ S q≠0}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and (hq.2.1.eventually_analyticAt.and
      ((continuousAt_const.eventually_lt
        (Complex.continuous_im.continuousAt.comp hq.1.continuousAt) hq.2.2.1).and (hq.2.1.continuousAt.eventually_ne hq.2.2.2)))
  obtain ⟨r,hr,htube⟩ := compact_product_tube hQ hU
    (fun eta heta=>⟨hBa eta heta,hSa eta heta,hB eta heta,hS eta heta⟩)
  exact ⟨r/2,half_pos hr,fun eta heta u hu=>htube eta heta u (hu.trans_lt (half_lt_self hr))⟩

/-- Every scalar trace of a joint compact family has common geometric jet
bounds on one fixed disk, chosen before the derivative order. -/
theorem compact_family_trace_geometric_jets {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] (H : ℂ × E→G) {Q : Set E} {ρ : ℝ}
    (hQ : IsCompact Q) (hρ : 0<ρ)
    (hH : ∀eta∈Q, ∀u : ℂ, ‖u‖≤ρ → AnalyticAt ℂ H (u,eta)) :
    ∀j : ℕ, ∃D : ℝ,1≤D ∧ ∀eta∈Q, ∀u : ℂ, ‖u‖<ρ/2 →
      ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℂ i (fun t=>H (t,eta)) u‖≤D^i := by
  let T : Set (ℂ × E) := closedBall 0 ρ ×ˢ Q
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hQ
  have hc : ContinuousOn H T := by
    intro q hq
    exact (hH q.2 hq.2 q.1 (by simpa using hq.1)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := hT.exists_bound_of_continuousOn hc
  let M' := max M 0
  have hM' : 0≤M' := le_max_right _ _
  intro j
  let J : ℕ→ℝ := fun i=>M'/(ρ/(2*((i+1:ℕ):ℝ)))^i
  have hJ (i : ℕ) : 0≤J i := by dsimp [J]; positivity
  let D := 1+∑i∈Finset.range (j+1),J i
  have hD : 1≤D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>hJ i))
  refine ⟨D,hD,?_⟩
  intro eta heta u hu i hi hij
  have ha : AnalyticOnNhd ℂ (fun t=>H (t,eta)) (ball 0 ρ) := by
    intro t ht
    exact (hH eta heta t (le_of_lt (by simpa using ht))).comp
      (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hn : ∀t∈ball (0:ℂ) ρ, ‖H (t,eta)‖≤M' := by
    intro t ht
    exact (hM (t,eta) ⟨ball_subset_closedBall ht,heta⟩).trans (le_max_left _ _)
  have hh := norm_iteratedFDeriv_le_on_half_ball i hρ hM' ha hn (by simpa using hu)
  have hsum := Finset.single_le_sum (fun k (_ : k∈Finset.range (j+1))=>hJ k)
    (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
  have hJD : J i≤D := by dsimp [D]; linarith
  exact hh.trans (hJD.trans (by simpa using pow_le_pow_right₀ hD hi))

/-- Common radius before all derivative orders, for the literal full angular
coefficients with nonconstant B and S on every compact complex family. -/
theorem compact_family_full_coefficient_tails {b : ℝ} (B S : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hBa : ∀eta∈Q, AnalyticAt ℂ B (0,eta))
    (hSa : ∀eta∈Q, AnalyticAt ℂ S (0,eta))
    (hB : ∀eta∈Q, 0<(B (0,eta)).im) (hS : ∀eta∈Q, S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ, ∃G : ℕ→ℝ, Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q, ∀u : ℂ, ‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (angularCoefficient (2*j+3+k) b
        (fun t=>B (t,eta)) (fun t=>S (t,eta))) u‖≤G k := by
  obtain ⟨ρ,hρ,htube⟩ := compact_admissible_family_tube B S hQ hBa hSa hB hS
  let T : Set (ℂ × E) := closedBall 0 ρ ×ˢ Q
  let H : ℂ × E→NumeratorParameter := fun q=>(q.1,(B q,S q))
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hQ
  have hH : ∀eta∈Q, ∀u : ℂ, ‖u‖≤ρ → AnalyticAt ℂ H (u,eta) :=
    fun eta heta u hu=>analyticAt_fst.prod ((htube eta heta u hu).1.prod (htube eta heta u hu).2.1)
  have hc : ContinuousOn (fun q=>(B q,S q)) T := by
    intro q hq
    have hh := htube q.2 hq.2 q.1 (by simpa using hq.1)
    exact (hh.1.continuousAt.prodMk hh.2.1.continuousAt).continuousWithinAt
  let K := (fun q=>(B q,S q)) '' T
  have hK : IsCompact K := hT.image_of_continuousOn hc
  have hKB : ∀v∈K,0<v.1.im := by
    rintro v ⟨q,hq,rfl⟩
    exact (htube q.2 hq.2 q.1 (by simpa using hq.1)).2.2.1
  have hKS : ∀v∈K,v.2≠0 := by
    rintro v ⟨q,hq,rfl⟩
    exact (htube q.2 hq.2 q.1 (by simpa using hq.1)).2.2.2
  obtain ⟨ε,hε,hjets⟩ := compact_actual_coefficient_summable_mixed_jets hb hK hKB hKS
  choose M hM hM0 hMb using hjets
  refine ⟨min (ρ/2) ε,lt_min (half_pos hρ) hε,?_⟩
  intro j
  obtain ⟨D,hD,hDj⟩ := compact_family_trace_geometric_jets H hQ hρ hH j
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
    ⟨hi,(htube eta heta u huρ').2.2⟩
  have hHu : H (u,eta)∈ball (0,(H (u,eta)).2) ε := by
    simp only [mem_ball,Prod.dist_eq,dist_zero_right,dist_self,max_lt_iff]
    exact ⟨hu.trans_le (min_le_right _ _),hε⟩
  have houter : ∀i≤j, ‖iteratedFDeriv ℂ i (independentAngularCoefficient (2*j+3+k) b) (H (u,eta))‖≤W k := by
    intro i hij
    have hh := hMb i (H (u,eta)).2 ⟨(u,eta),⟨by simpa using huρ',heta⟩,rfl⟩
      (H (u,eta)) hHu hi (2*(j-i)+k)
    rw [show 2*i+3+(2*(j-i)+k)=2*j+3+k by omega] at hh
    exact hh.trans (Finset.single_le_sum (f := fun a=>M a (2*(j-a)+k)) (fun a (_ : a∈Finset.range (j+1))=>hM0 a _)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega)))
  have htrace : AnalyticAt ℂ (fun t=>H (t,eta)) u :=
    (hH eta heta u huρ').comp (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hh := contDiffAt_composition_geometric_jets (f := fun t : ℂ=>H (t,eta)) j
    (independentAngularCoefficient_contDiffAt _ j hHp) htrace.contDiffAt houter
    (hDj eta heta u huρ)
  have heq : (independentAngularCoefficient (2*j+3+k) b ∘ (fun t=>H (t,eta)))=
      angularCoefficient (2*j+3+k) b (fun t=>B (t,eta)) (fun t=>S (t,eta)) := by
    funext t
    rfl
  rw [heq,norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

end
end IsingBulk.Joint.RegularEdges
