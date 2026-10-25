import IsingBulk.Joint.FormFactors.CompactFamilyMixedTails

/-! Full mixed family tails for a general joint parameter substitution.
The first model coordinate is the actual edge function, not assumed to equal
the external scalar coordinate away from the compact parameter set. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.Joint.RegularEdges IsingBulk.Joint.Negative Set Filter Metric
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Arbitrary compact analytic families admit summable envelopes for every
ambient mixed derivative of the actual full coefficient times an analytic
prefactor. The same scalar radius works before every derivative order. -/
theorem compact_joint_parametric_coefficient_mixed_tails {b : ℝ}
    (H : ℂ × E→NumeratorParameter) (A : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q)
    (hHa : ∀eta∈Q,AnalyticAt ℂ H (0,eta))
    (hAa : ∀eta∈Q,AnalyticAt ℂ A (0,eta))
    (hH0 : ∀eta∈Q,(H (0,eta)).1=0)
    (hB : ∀eta∈Q,0<(H (0,eta)).2.1.im)
    (hS : ∀eta∈Q,(H (0,eta)).2.2≠0) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<(H (u,eta)).1.im → ∀k : ℕ,
        ‖iteratedFDeriv ℂ j (fun q=>A q*independentAngularCoefficient (2*j+3+k) b (H q)) (u,eta)‖≤G k := by
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ H q ∧ AnalyticAt ℂ A q ∧
    0<(H q).2.1.im ∧ (H q).2.2≠0}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and (hq.2.1.eventually_analyticAt.and
      ((continuousAt_const.eventually_lt
        (Complex.continuous_im.continuousAt.comp hq.1.continuousAt.snd.fst) hq.2.2.1).and
        (hq.1.continuousAt.snd.snd.eventually_ne hq.2.2.2)))
  obtain ⟨r,hr,htube⟩ := compact_product_tube hQ hU
    (fun eta heta=>⟨hHa eta heta,hAa eta heta,hB eta heta,hS eta heta⟩)
  let ρ := r/2
  have hρ : 0<ρ := half_pos hr
  let T : Set (ℂ × E) := closedBall 0 ρ ×ˢ Q
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hQ
  have hdata (q : ℂ × E) (hq : q∈T) : q∈U :=
    htube q.2 hq.2 q.1 ((show ‖q.1‖≤ρ by simpa using hq.1).trans_lt (half_lt_self hr))
  have hf : AnalyticOnNhd ℂ H T := fun q hq=>(hdata q hq).1
  have ha : AnalyticOnNhd ℂ A T := fun q hq=>(hdata q hq).2.1
  let K := (fun q=> (H q).2) '' T
  have hK : IsCompact K := hT.image_of_continuousOn hf.continuousOn.snd
  have hKB : ∀v∈K,0<v.1.im := by rintro v ⟨q,hq,rfl⟩; exact (hdata q hq).2.2.1
  have hKS : ∀v∈K,v.2≠0 := by rintro v ⟨q,hq,rfl⟩; exact (hdata q hq).2.2.2
  obtain ⟨ε,hε,hjets⟩ := compact_actual_coefficient_summable_mixed_jets hb hK hKB hKS
  choose M hM hM0 hMb using hjets
  let V : Set (ℂ × E) := {q | AnalyticAt ℂ H q ∧ ‖(H q).1‖<ε}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      (hq.1.continuousAt.fst.norm.eventually_lt continuousAt_const hq.2)
  obtain ⟨s,hs,hsmall⟩ := compact_product_tube hQ hV
    (fun eta heta=>⟨hHa eta heta,by simpa only [hH0 eta heta,norm_zero] using hε⟩)
  let δ := min ρ s
  have hδ : 0<δ := lt_min hρ hs
  have hp (eta : E) (heta : eta∈Q) (u : ℂ) (hu : ‖u‖<δ) (hi : 0<(H (u,eta)).1.im) :
      (u,eta)∈T ∧ H (u,eta)∈independentUpperDomain ∧ H (u,eta)∈ball (0,(H (u,eta)).2) ε := by
    have hq : (u,eta)∈T := ⟨by simpa using (hu.trans_le (min_le_left _ _)).le,heta⟩
    refine ⟨hq,⟨hi,(hdata (u,eta) hq).2.2⟩,?_⟩
    simp only [mem_ball,Prod.dist_eq,dist_zero_right,dist_self,max_lt_iff]
    exact ⟨(hsmall eta heta u (hu.trans_le (min_le_right _ _))).2,hε⟩
  refine ⟨δ,hδ,?_⟩
  intro j
  obtain ⟨D,hD,hfD⟩ := compact_joint_analytic_geometric_jets hT hf j
  choose C hC haC using (fun i : ℕ=>compact_joint_analytic_jets_bound hT ha i)
  let L := 1+∑i∈Finset.range (j+1),C i
  have hL : 0<L := by
    have hh : 0≤∑i∈Finset.range (j+1),C i := Finset.sum_nonneg (fun i _=>(hC i).le)
    dsimp [L]; linarith
  have hCL (i : ℕ) (hi : i≤j) : C i≤L := by
    have hh := Finset.single_le_sum (fun a (_ : a∈Finset.range (j+1))=>(hC a).le)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
    dsimp [L]; linarith
  let W : ℕ→ℝ := fun k=>∑i∈Finset.range (j+1),M i (2*(j-i)+k)
  have hW (k : ℕ) : 0≤W k := Finset.sum_nonneg (fun i _=>hM0 i _)
  have hWs : Summable W := by
    apply summable_sum
    intro i _
    exact (hM i).comp_injective (i:=fun k : ℕ=>2*(j-i)+k) (by intro a c he; dsimp at he; omega)
  let J : ℝ := (j.factorial:ℝ)*D^j
  have hJ : 0≤J := by dsimp [J]; positivity
  refine ⟨fun k=>(2^j*L*J)*W k,hWs.mul_left _,
    fun k=>mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hL.le) hJ) (hW k),?_⟩
  intro eta heta u hu hi k
  have hd := hp eta heta u hu hi
  have hg : ContDiffAt ℂ j (fun q=>independentAngularCoefficient (2*j+3+k) b (H q)) (u,eta) :=
    (independentAngularCoefficient_contDiffAt _ j hd.2.1).comp (u,eta) (hf (u,eta) hd.1).contDiffAt
  have houter (i : ℕ) (hij : i≤j) :
      ‖iteratedFDeriv ℂ i (independentAngularCoefficient (2*j+3+k) b) (H (u,eta))‖≤W k := by
    have hh := hMb i (H (u,eta)).2 ⟨(u,eta),hd.1,rfl⟩ (H (u,eta)) hd.2.2 hi (2*(j-i)+k)
    rw [show 2*i+3+(2*(j-i)+k)=2*j+3+k by omega] at hh
    exact hh.trans (Finset.single_le_sum (f:=fun a=>M a (2*(j-a)+k))
      (fun a (_ : a∈Finset.range (j+1))=>hM0 a _)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega)))
  have hcomp (i : ℕ) (hij : i≤j) :
      ‖iteratedFDeriv ℂ i (fun q=>independentAngularCoefficient (2*j+3+k) b (H q)) (u,eta)‖≤J*W k := by
    have hh := contDiffAt_composition_geometric_jets i
      (independentAngularCoefficient_contDiffAt _ i hd.2.1) (hf (u,eta) hd.1).contDiffAt
      (fun a ha=>houter a (ha.trans hij)) (fun a ha haj=>hfD (u,eta) hd.1 a ha (haj.trans hij))
    apply hh.trans
    have hfac : (i.factorial:ℝ)≤j.factorial := by exact_mod_cast Nat.factorial_le hij
    have hpow := pow_le_pow_right₀ hD hij
    dsimp [J]
    nlinarith [mul_le_mul hfac hpow (pow_nonneg (by linarith : 0≤D) i) (Nat.cast_nonneg j.factorial),hW k]
  have hh := contDiffAt_product_uniform_jets j j le_rfl (ha (u,eta) hd.1).contDiffAt hg
    hL.le (mul_nonneg hJ (hW k)) (fun i hi=>(haC i (u,eta) hd.1).trans (hCL i hi)) hcomp
  simpa only [mul_assoc] using hh

end
end IsingBulk.Joint.FormFactors
