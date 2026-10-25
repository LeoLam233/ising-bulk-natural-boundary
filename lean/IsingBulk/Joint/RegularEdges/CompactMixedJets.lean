import IsingBulk.Joint.RegularEdges.UniformFullNumerator
import IsingBulk.Joint.RegularEdges.MixedCauchy
import Mathlib.Topology.MetricSpace.Thickening

/-! # Common compact-family polydisks for all mixed numerator jets
The radii are chosen before the point, particle number, angular variables and
derivative order. Product norms make these literal independent polydisks.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

theorem compact_full_numerator_polydisks {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ v∈K, ∀ (N : ℕ) (q : Fin N → ℝ),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      AnalyticOnNhd ℂ (fun p => independentNumerator b p (List.ofFn q)) (ball (0,v) δ) ∧
      ∀ p∈ball (0,v) δ,
        ‖independentNumerator b p (List.ofFn q)‖≤particleEdgeMajorant r C M N := by
  let V : Set (ℂ × ℂ) := {v | 0<v.1.im ∧ v.2≠0}
  have hV : IsOpen V := (isOpen_lt continuous_const
    (Complex.continuous_im.comp continuous_fst)).inter (isOpen_ne_fun continuous_snd continuous_const)
  obtain ⟨η,hη,hηV⟩ := hK.exists_cthickening_subset_open hV (fun v hv => ⟨hB v hv,hS v hv⟩)
  let L := cthickening η K
  have hL : IsCompact L := hK.cthickening
  have hLB : ∀ v∈L, 0<v.1.im := fun v hv => (hηV hv).1
  have hLS : ∀ v∈L, v.2≠0 := fun v hv => (hηV hv).2
  have hLK : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hLi : ∀ B∈Prod.fst '' L, 0<B.im := by rintro B ⟨v,hv,rfl⟩; exact hLB v hv
  obtain ⟨δ₁,r,C,M,hδ₁,hr,hr1,hC,hM,hbound⟩ := compact_full_numerator hb hL hLB hLS
  obtain ⟨δ₂,r₂,C₂,hδ₂,_,_,_,hroot⟩ := compact_parameter_disk hb hLK hLi
  obtain ⟨δ₃,hδ₃,hden⟩ := compact_denominator_disk hb hLK hLi
  let δ := min η (min δ₁ (min δ₂ δ₃))
  have hδ : 0<δ := lt_min hη (lt_min hδ₁ (lt_min hδ₂ hδ₃))
  have hp (v : ℂ × ℂ) (hv : v∈K) (p : NumeratorParameter) (hp : p∈ball (0,v) δ) :
      p.2∈L ∧ ‖p.1‖<δ₁ ∧ ‖p.1‖<δ₂ ∧ ‖p.1‖<δ₃ := by
    have hh : ‖p.1‖<δ ∧ dist p.2 v<δ := by
      simpa only [mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right] using hp
    refine ⟨mem_cthickening_of_dist_le p.2 v η K hv
      (hh.2.le.trans (min_le_left _ _)),?_,?_,?_⟩
    · exact hh.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    · exact hh.1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact hh.1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,?_⟩
  intro v hv N q hq
  constructor
  · intro p hpball
    have hh := hp v hv p hpball
    exact independentNumerator_analyticAt q (hLS p.2 hh.1)
      (fun i => (hroot p.1 p.2.1 hh.2.2.1 ⟨p.2,hh.1,rfl⟩).1 (q i) (hq i))
      (fun i j => hden p.1 p.2.1 hh.2.2.2 ⟨p.2,hh.1,rfl⟩ (q i) (hq i) (q j) (hq j))
  · intro p hpball
    have hh := hp v hv p hpball
    exact hbound p.1 hh.2.1 p.2 hh.1 N q hq

/-- Uniform operator-norm bounds for every mixed derivative, on one fixed inner
polydisk and for every member of an arbitrary compact admissible family. -/
theorem compact_full_numerator_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ v∈K, ∀ (N k : ℕ) (q : Fin N → ℝ),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → ∀ p∈ball (0,v) (δ/2),
      ‖iteratedFDeriv ℂ k (fun p => independentNumerator b p (List.ofFn q)) p‖≤
        particleEdgeMajorant r C M N/(δ/(2*((k+1:ℕ):ℝ)))^k := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hall⟩ := compact_full_numerator_polydisks hb hK hB hS
  refine ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,?_⟩
  intro v hv N k q hq p hp
  have hh := hall v hv N q hq
  exact norm_iteratedFDeriv_le_on_half_ball k hδ
    (particleEdgeMajorant_nonneg hr.le hC.le hM.le N) hh.1 hh.2 hp

/-- Summable dominating sequences for all mixed jets, with a single compact-family
polydisk. No coefficient or tail majorant is supplied as a premise. -/
theorem compact_full_numerator_summable_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∃ G : ℕ → ℕ → ℝ,
      (∀ k, Summable (G k)) ∧ (∀ k N, 0≤G k N) ∧
      ∀ v∈K, ∀ (N k : ℕ) (q : Fin N → ℝ),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) → ∀ p∈ball (0,v) δ,
      ‖iteratedFDeriv ℂ k (fun p => independentNumerator b p (List.ofFn q)) p‖≤G k N := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hall⟩ := compact_full_numerator_mixed_jets hb hK hB hS
  refine ⟨δ/2,half_pos hδ,fun k N => particleEdgeMajorant r C M N/(δ/(2*((k+1:ℕ):ℝ)))^k,?_,?_,hall⟩
  · intro k
    have hs : Summable (fun N => particleEdgeMajorant r C M N) := by
      simpa only [pow_zero,one_mul] using particleEdgeMajorant_polynomial_summable hr hr1 hC hM 0
    exact hs.div_const _
  · intro k N
    exact div_nonneg (particleEdgeMajorant_nonneg hr.le hC.le hM.le N) (by positivity)

end
end IsingBulk.Joint.RegularEdges
