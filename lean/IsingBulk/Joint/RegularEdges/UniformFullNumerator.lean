import IsingBulk.Joint.RegularEdges.UniformNumerator
import IsingBulk.Anisotropic.RegularEdges.TailSummability
import IsingBulk.Anisotropic.RegularEdges.AngularNumeratorBridge

/-! # Complete numerator estimates for independent complex parameters
The one-body scale is a third independent complex parameter. Compact-family
bounds below contain all factors of the numerator and every particle number.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators

abbrev NumeratorParameter := ℂ × (ℂ × ℂ)

def independentNumerator (b : ℝ) (p : NumeratorParameter) (qs : List ℝ) : ℂ :=
  edgeNumerator b (fun _ => p.2.1) (fun _ => p.2.2) p.1 qs

def independentOneBody (b : ℝ) (p : NumeratorParameter) (q : ℝ) : ℂ :=
  2*root b (p.1,p.2.1) q/(p.2.2*(1-(root b (p.1,p.2.1) q)^2))

theorem compact_oneBody_bound {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ u : ℂ, ‖u‖<δ → ∀ v∈K,
      ∀ q∈Icc (-Real.pi) Real.pi, ‖independentOneBody b (u,v) q‖≤M := by
  let L := K ×ˢ Icc (-Real.pi) Real.pi
  have hL : IsCompact L := hK.prod isCompact_Icc
  have hc (x : (ℂ × ℂ) × ℝ) (hx : x∈L) :
      ContinuousAt (fun y : ℂ × ((ℂ × ℂ) × ℝ) => independentOneBody b (y.1,y.2.1) y.2.2) (0,x) := by
    have hr := (root_continuousAt (show dispersion b (0,x.1.1) x.2∈continuedRootDomain by
      simpa using edgeW_domain hb (hB x.1 hx.1) x.2)).comp
      (x := ((0:ℂ),x)) (f := fun y : ℂ × ((ℂ × ℂ) × ℝ) => ((y.1,y.2.1.1),y.2.2)) (by fun_prop)
    exact (continuousAt_const.mul hr).div
      ((continuousAt_snd.comp (continuousAt_fst.comp continuousAt_snd)).mul
        (continuousAt_const.sub (hr.pow 2)))
      (mul_ne_zero (hS x.1 hx.1) (by simpa only [root_zero,pow_two] using
        edgeRoot_pair_denominator_ne_zero hb (hB x.1 hx.1) x.2 x.2))
  have hc0 : ContinuousOn (fun x : (ℂ × ℂ) × ℝ => independentOneBody b (0,x.1) x.2) L := by
    intro x hx
    exact ((hc x hx).comp (f := fun x : (ℂ × ℂ) × ℝ => ((0:ℂ),x))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := hL.exists_bound_of_continuousOn hc0
  let C := max M 0+1
  have hC : 0<C := by dsimp [C]; linarith [le_max_right M 0]
  have he : ∀ᶠ u : ℂ in 𝓝 0, ∀ x∈L, ‖independentOneBody b (u,x.1) x.2‖<C := by
    apply hL.eventually_forall_of_forall_eventually
    intro x hx
    exact (hc x hx).norm.eventually_lt continuousAt_const
      ((hM x hx).trans_lt (by dsimp [C]; linarith [le_max_left M 0]))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨δ,C,hδ,hC,fun u hu v hv q hq =>
    (hδb (show u∈ball (0:ℂ) δ by simpa using hu) (v,q) ⟨hv,hq⟩).le⟩

/-- Full all-particle Schur Gaussian bounds, with the one-body factors included,
for every member of a compact admissible complex anisotropy/scale family. -/
theorem compact_full_numerator {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ u : ℂ, ‖u‖<δ → ∀ v∈K, ∀ (N : ℕ) (q : Fin N → ℝ),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      ‖independentNumerator b (u,v) (List.ofFn q)‖≤particleEdgeMajorant r C M N := by
  have hBK : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hBi : ∀ B∈Prod.fst '' K, 0<B.im := by rintro B ⟨v,hv,rfl⟩; exact hB v hv
  obtain ⟨δ,r,C,hδ,hr,hr1,hC,hpair⟩ := compact_complete_pairs hb hBK hBi
  obtain ⟨ε,M,hε,hM,hone⟩ := compact_oneBody_bound hb hK hB hS
  refine ⟨min δ ε,r,C,M,lt_min hδ hε,hr,hr1,hC,hM,?_⟩
  intro u hu v hv N q hq
  have hp := hpair u v.1 (hu.trans_le (min_le_left _ _)) ⟨v,hv,rfl⟩
  have hqs : ∀ a∈List.ofFn q, a∈Icc (-Real.pi) Real.pi := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hq i
  have ho : ‖((List.ofFn q).map (edgeOneBody b (fun _ => v.1) (fun _ => v.2) u)).prod‖≤M^N := by
    simpa only [List.length_ofFn] using norm_list_product_le
      (edgeOneBody b (fun _ => v.1) (fun _ => v.2) u) (List.ofFn q) hM.le
      (fun a ha => hone u (hu.trans_le (min_le_right _ _)) v hv a (hqs a ha))
  by_cases hpar : N%2=0
  · have hp' := hp.1 (N/2) (List.ofFn q) (by simp only [List.length_ofFn]; omega) hqs
    have hN : N=2*(N/2) := by omega
    have ho' := ho.trans_eq (congrArg (fun n : ℕ => M^n) hN)
    rw [independentNumerator,edgeNumerator,norm_mul]
    have hh := mul_le_mul hp' ho' (norm_nonneg _) (by positivity)
    simpa only [particleEdgeMajorant,ite_eq_left hpar,evenEdgeMajorant,mul_assoc,mul_comm,mul_left_comm] using hh
  · have hp' := hp.2 (N/2) (List.ofFn q) (by simp only [List.length_ofFn]; omega) hqs
    have hN : N=2*(N/2)+1 := by omega
    have ho' := ho.trans_eq (congrArg (fun n : ℕ => M^n) hN)
    rw [independentNumerator,edgeNumerator,norm_mul]
    have hh := mul_le_mul hp' ho' (norm_nonneg _) (by positivity)
    simpa only [particleEdgeMajorant,ite_eq_right hpar,oddEdgeMajorant,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Genuine analyticity in all three independent complex parameters. -/
theorem independentNumerator_analyticAt {b : ℝ} {p : NumeratorParameter} {N : ℕ}
    (q : Fin N → ℝ) (hS : p.2.2≠0)
    (hdom : ∀ i, dispersion b (p.1,p.2.1) (q i)∈continuedRootDomain)
    (hden : ∀ i j, 1-root b (p.1,p.2.1) (q i)*root b (p.1,p.2.1) (q j)≠0) :
    AnalyticAt ℂ (fun v => independentNumerator b v (List.ofFn q)) p := by
  have hB : AnalyticAt ℂ (fun v : NumeratorParameter => v.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hSa : AnalyticAt ℂ (fun v : NumeratorParameter => v.2.2) p := analyticAt_snd.comp analyticAt_snd
  have hr (i : Fin N) : AnalyticAt ℂ (fun v : NumeratorParameter => root b (v.1,v.2.1) (q i)) p :=
    (root_analyticAt (hdom i)).comp
      (f := fun v : NumeratorParameter => (v.1,v.2.1)) (analyticAt_fst.prod hB)
  simp_rw [independentNumerator,edgeNumerator_eq_indexed]
  change AnalyticAt ℂ (fun v : NumeratorParameter =>
    v.2.1^(N.choose 2)*(v.2.2)⁻¹^N *
      (∏ i, 2*root b (v.1,v.2.1) (q i)/(1-root b (v.1,v.2.1) (q i)^2)) *
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
        angularRootPair (root b (v.1,v.2.1) (q i)) (root b (v.1,v.2.1) (q j)) (q i) (q j))) p
  refine (((hB.pow _).mul ((hSa.inv hS).pow _)).mul ?_).mul ?_
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (hr i)).div (analyticAt_const.sub ((hr i).pow 2))
      (by simpa only [pow_two] using hden i i)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod
    intro j _
    exact (((analyticAt_const.mul (hr i)).mul (hr j)).mul analyticAt_const).div
      ((analyticAt_const.sub ((hr i).mul (hr j))).pow 2) (pow_ne_zero 2 (hden i j))

end
end IsingBulk.Joint.RegularEdges
