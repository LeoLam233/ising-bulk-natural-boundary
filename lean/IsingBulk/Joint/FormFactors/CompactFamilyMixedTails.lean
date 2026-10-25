import IsingBulk.Joint.RegularEdges.FamilyTailJets

/-! All mixed derivatives in the full complex edge-plus-parameter space.
Only compactness of the parameter set is used; the parameter space need not
be finite dimensional or locally compact. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Joint.RegularEdges
  IsingBulk.Joint.Negative Set Filter Metric
open scoped Topology BigOperators

/-- Compact joint analytic germs bound every full ambient Frechet jet. -/
theorem compact_joint_analytic_jets_bound {X G : Type}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {f : X→G} {K : Set X} (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (j : ℕ) :
    ∃M : ℝ,0<M ∧ ∀q∈K,‖iteratedFDeriv ℂ j f q‖≤M := by
  have hc : ContinuousOn (iteratedFDeriv ℂ j f) K := by
    intro q hq
    have hh : ContDiffAt ℂ j f q := (hf q hq).contDiffAt
    exact (hh.continuousAt_iteratedFDeriv le_rfl).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨max M 0+1,by linarith [le_max_right M 0],fun q hq=>
    (hM q hq).trans (by linarith [le_max_left M 0])⟩

/-- A finite set of full ambient jet orders has a common geometric bound. -/
theorem compact_joint_analytic_geometric_jets {X G : Type}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {f : X→G} {K : Set X} (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (j : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ q ∈ K, ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℂ i f q‖ ≤ D ^ i := by
  choose M hM hb using (fun i : ℕ=>compact_joint_analytic_jets_bound hK hf i)
  let D := 1+∑i∈Finset.range (j+1),M i
  have hD : 1≤D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>(hM i).le))
  refine ⟨D,hD,?_⟩
  intro q hq i hi hij
  have hm := Finset.single_le_sum (fun a (_ : a∈Finset.range (j+1))=>(hM a).le)
    (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
  have hMD : M i≤D := by dsimp [D]; linarith
  exact (hb i q hq).trans (hMD.trans (by simpa using pow_le_pow_right₀ hD hi))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One common radius precedes every mixed derivative order, for the actual
complete angular coefficient on an arbitrary compact joint analytic family. -/
theorem compact_family_full_coefficient_mixed_tails {b : ℝ} (B S : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hBa : ∀eta∈Q, AnalyticAt ℂ B (0,eta))
    (hSa : ∀eta∈Q, AnalyticAt ℂ S (0,eta))
    (hB : ∀eta∈Q, 0<(B (0,eta)).im) (hS : ∀eta∈Q, S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ, ∃G : ℕ→ℝ, Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q, ∀u : ℂ, ‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q : ℂ × E=>angularCoefficient (2*j+3+k) b
        (fun t=>B (t,q.2)) (fun t=>S (t,q.2)) q.1) (u,eta)‖≤G k := by
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
  obtain ⟨D,hD,hDj⟩ := compact_joint_analytic_geometric_jets hT
    (show AnalyticOnNhd ℂ H T from fun q hq=>hH q.2 hq.2 q.1 (by simpa using hq.1)) j
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
  have hh := contDiffAt_composition_geometric_jets (f := H) j
    (independentAngularCoefficient_contDiffAt _ j hHp) (hH eta heta u huρ').contDiffAt houter
    (hDj (u,eta) ⟨by simpa using huρ',heta⟩)
  have heq : (independentAngularCoefficient (2*j+3+k) b ∘ H)=
      (fun q : ℂ × E=>angularCoefficient (2*j+3+k) b
        (fun t=>B (t,q.2)) (fun t=>S (t,q.2)) q.1) := by
    funext q
    rfl
  rw [heq] at hh
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

end
end IsingBulk.Joint.FormFactors
