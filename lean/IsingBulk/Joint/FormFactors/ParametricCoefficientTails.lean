import IsingBulk.Joint.FormFactors.CompositionJets
import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets

/-! Complete coefficient mixed tails after a genuine holomorphic family
substitution, including an arbitrary analytic physical amplitude. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Joint.RegularEdges

/-- The radius is chosen before the derivative order. Finite sums of reindexed
all-particle envelopes control the chain rule and the physical amplitude. -/
theorem compact_parametric_coefficient_tails {b : ℝ} (hb : |b|<1)
    {C : Set Coupling} (hC : IsCompact C) {q₀ : Coupling} (hCq : C∈𝓝 q₀)
    (hq₀ : q₀.1=0) {f : Coupling → NumeratorParameter} {amp : Coupling → ℂ}
    (hf : AnalyticOnNhd ℂ f C) (ha : AnalyticOnNhd ℂ amp C)
    (hu : ∀ q∈C, (f q).1=q.1)
    (hB : ∀ q∈C, 0<(f q).2.1.im) (hS : ∀ q∈C, (f q).2.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
      Summable G ∧ (∀ k, 0≤G k) ∧ ∀ q∈ball q₀ δ, 0<q.1.im → ∀ k : ℕ,
      ‖iteratedFDeriv ℂ j
        (fun t => amp t*independentAngularCoefficient (2*j+3+k) b (f t)) q‖≤G k := by
  let K : Set (ℂ × ℂ) := (fun q => (f q).2) '' C
  have hK : IsCompact K := hC.image_of_continuousOn hf.continuousOn.snd
  have hKB : ∀ v∈K, 0<v.1.im := by rintro v ⟨q,hq,rfl⟩; exact hB q hq
  have hKS : ∀ v∈K, v.2≠0 := by rintro v ⟨q,hq,rfl⟩; exact hS q hq
  obtain ⟨ε,hε,hjets⟩ := compact_actual_coefficient_summable_mixed_jets hb hK hKB hKS
  choose M hM hM0 hMb using hjets
  obtain ⟨r,hr,hrC⟩ := Metric.mem_nhds_iff.mp hCq
  let δ := min r ε
  have hδ : 0<δ := lt_min hr hε
  have hp (q : Coupling) (hq : q∈ball q₀ δ) (hi : 0<q.1.im) :
      q∈C ∧ f q∈independentUpperDomain ∧ f q∈ball (0,(f q).2) ε := by
    have hqC := hrC (ball_subset_ball (min_le_left r ε) hq)
    have hqn : ‖q.1‖<ε := by
      have hh : dist q.1 q₀.1<δ := (max_lt_iff.mp (show max (dist q.1 q₀.1) (dist q.2 q₀.2)<δ from hq)).1
      simpa only [hq₀,dist_zero_right] using hh.trans_le (min_le_right r ε)
    refine ⟨hqC,⟨by rwa [hu q hqC],hB q hqC,hS q hqC⟩,?_⟩
    simp only [mem_ball,Prod.dist_eq,dist_zero_right,dist_self,max_lt_iff,hu q hqC]
    exact ⟨hqn,hε⟩
  refine ⟨δ,hδ,?_⟩
  intro j
  obtain ⟨D,hD,hfD⟩ := compact_analytic_geometric_jets hC hf j
  choose A hA haA using (fun i : ℕ => compact_analytic_all_jets_bound hC ha i)
  let H := 1+∑ i∈Finset.range (j+1), A i
  have hH : 0<H := by
    have hs : 0≤∑ i∈Finset.range (j+1), A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp [H]; linarith
  have hAH (i : ℕ) (hi : i≤j) : A i≤H := by
    have hh := Finset.single_le_sum (fun a (_ : a∈Finset.range (j+1)) => (hA a).le)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
    dsimp [H]; linarith
  let B : ℕ→ℝ := fun k => ∑ i∈Finset.range (j+1), M i (2*(j-i)+k)
  have hB0 (k : ℕ) : 0≤B k := Finset.sum_nonneg (fun i _ => hM0 i _)
  have hBs : Summable B := by
    apply summable_sum
    intro i _
    exact (hM i).comp_injective (i := fun k : ℕ => 2*(j-i)+k) (by intro a c he; dsimp at he; omega)
  let L : ℝ := (j.factorial:ℝ)*D^j
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨fun k => (2^j*H*L)*B k,hBs.mul_left _,fun k => mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hH.le) hL) (hB0 k),?_⟩
  intro q hq hi k
  have hd := hp q hq hi
  have hg : ContDiffAt ℂ j (fun t => independentAngularCoefficient (2*j+3+k) b (f t)) q :=
    (independentAngularCoefficient_contDiffAt _ j hd.2.1).comp q (hf q hd.1).contDiffAt
  have houter (i : ℕ) (hij : i≤j) :
      ‖iteratedFDeriv ℂ i (independentAngularCoefficient (2*j+3+k) b) (f q)‖≤B k := by
    have hh := hMb i (f q).2 ⟨q,hd.1,rfl⟩ (f q) hd.2.2 (by rwa [hu q hd.1]) (2*(j-i)+k)
    rw [show 2*i+3+(2*(j-i)+k)=2*j+3+k by omega] at hh
    apply hh.trans
    exact Finset.single_le_sum (f := fun a => M a (2*(j-a)+k))
      (fun a (_ : a∈Finset.range (j+1)) => hM0 a _)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
  have hcomp (i : ℕ) (hij : i≤j) :
      ‖iteratedFDeriv ℂ i (fun t => independentAngularCoefficient (2*j+3+k) b (f t)) q‖≤L*B k := by
    have hh := contDiffAt_composition_geometric_jets i
      (independentAngularCoefficient_contDiffAt _ i hd.2.1) ((hf q hd.1).contDiffAt)
      (fun a ha => houter a (ha.trans hij)) (fun a ha haj => hfD q hd.1 a ha (haj.trans hij))
    apply hh.trans
    have hfac : (i.factorial:ℝ)≤j.factorial := by exact_mod_cast Nat.factorial_le hij
    have hpow := pow_le_pow_right₀ hD hij
    dsimp [L]
    nlinarith [mul_le_mul hfac hpow (pow_nonneg (by linarith : 0≤D) i) (Nat.cast_nonneg j.factorial),hB0 k]
  have hh := contDiffAt_product_uniform_jets j j le_rfl (ha q hd.1).contDiffAt hg
    hH.le (mul_nonneg hL (hB0 k)) (fun i hi => (haA i q hd.1).trans (hAH i hi)) hcomp
  simpa only [mul_assoc] using hh

end
end IsingBulk.Joint.FormFactors
