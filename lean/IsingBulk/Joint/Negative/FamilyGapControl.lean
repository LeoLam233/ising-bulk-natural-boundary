import IsingBulk.Joint.Negative.FamilyFullControl
import IsingBulk.Anisotropic.NegativeDominance.GapFullDiskControl

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
  IsingBulk.Anisotropic.NegativeDominance IsingBulk.Joint.RegularEdges Set Metric
open scoped Topology BigOperators

/-- A derived positive boundary gap persists on a common independent a/N
polydisk. This analytic lemma is shared by the outer and nonresonant estimates. -/
theorem compact_root_product_disk_of_boundary_gap {b : ℝ} {Q : Set (ℂ × ℂ)}
    (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀v∈Q, 0<v.1.im) (hS : ∀v∈Q, v.2≠0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a : ℝ,0<a ∧ ∀v∈Q, ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b v.1 (q i)‖ →
      ∀p∈ball ((0:ℂ),v) (a/(N:ℝ)),
      (∀i,AnalyticAt ℂ (fun x=>independentRoot b x (q i)) p) ∧
      κ/2≤‖1-∏i,independentRoot b p (q i)‖ := by
  obtain ⟨δ,L,hδ,hL,hroot⟩ := compact_root_lipschitz hb hQ hB hS
  let E := Real.exp 1
  have hE : 0<E := Real.exp_pos _
  have hE1 : 1≤E := Real.one_le_exp_iff.mpr (by norm_num)
  let a := min δ (min (1/(E*L)) (κ/(2*E*L)))
  have ha : 0<a := lt_min hδ (lt_min (by positivity) (by positivity))
  have haδ : a≤δ := min_le_left _ _
  have ha1 : a≤1/(E*L) := (min_le_right _ _).trans (min_le_left _ _)
  have haκ : a≤κ/(2*E*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hELa : E*L*a≤1 := by have hh := (le_div_iff₀ (mul_pos hE hL)).mp ha1; nlinarith
  have hELκ : E*L*a≤κ/2 := by have hh := (le_div_iff₀ (by positivity : 0<2*E*L)).mp haκ; nlinarith
  refine ⟨a,ha,?_⟩
  intro v hv N hN q hq hgap p hp
  let u := ‖p-((0:ℂ),v)‖
  have hu : u<a/(N:ℝ) := by simpa only [mem_ball,dist_eq_norm] using hp
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hscale : (N : ℝ)*u≤a := by have hh := (lt_div_iff₀ hNp).mp hu; nlinarith
  have hau : a/(N : ℝ)≤a := (div_le_iff₀ hNp).mpr (by nlinarith)
  have huδ : u<δ := hu.trans_le (hau.trans haδ)
  have hNd : (N : ℝ)*(L*u)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hscale hL.le
    have he := mul_le_mul_of_nonneg_right hE1 (show 0≤L*a by positivity)
    nlinarith
  have hbase (i : Fin N) : ‖independentRoot b (0,v) (q i)‖≤1 := by
    simpa only [independentRoot,root_zero] using (edgeRoot_bounds hb (hB v hv) (q i)).1
  have hdif (i : Fin N) : ‖independentRoot b p (q i)-independentRoot b (0,v) (q i)‖≤L*u :=
    (hroot v hv p (by simpa only [mem_ball,dist_eq_norm] using huδ) (q i) (hq i)).2
  have hp := norm_prod_perturbation_linear (fun i=>independentRoot b p (q i))
    (fun i=>independentRoot b (0,v) (q i)) (by positivity : 0≤L*u) hNd hbase hdif
  have herr : E*(N : ℝ)*(L*u)≤κ/2 := by
    have hh := mul_le_mul_of_nonneg_left hscale (mul_pos hE hL).le
    nlinarith
  have htri := norm_add_le
    ((∏i, independentRoot b p (q i))-(∏i, independentRoot b (0,v) (q i))) (1-(∏i, independentRoot b p (q i)))
  rw [show ((∏i, independentRoot b p (q i))-(∏i, independentRoot b (0,v) (q i)))+(1-(∏i, independentRoot b p (q i)))=
    1-(∏i, independentRoot b (0,v) (q i)) by ring] at htri
  change ‖(∏i, independentRoot b p (q i))-(∏i, independentRoot b (0,v) (q i))‖≤E*(N : ℝ)*(L*u) at hp
  have hgap' : κ≤‖1-∏i,independentRoot b (0,v) (q i)‖ := by
    simpa only [independentRoot,root_zero] using hgap
  exact ⟨fun i=>(hroot v hv p (by simpa only [mem_ball,dist_eq_norm] using huδ) (q i) (hq i)).1,by linarith⟩


theorem compact_full_integrand_disk_of_boundary_gap {b : ℝ} {Q : Set (ℂ × ℂ)}
    (hb : |b|<1) (hQ : IsCompact Q) (hB : ∀v∈Q, 0<v.1.im) (hS : ∀v∈Q, v.2≠0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀v∈Q, ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b v.1 (q i)‖ →
      ∀p∈ball ((0:ℂ),v) (a/(N:ℝ)),
      AnalyticAt ℂ (fun x=>independentFullIntegrand b x q) p ∧
      ‖independentFullIntegrand b p q‖≤K*particleEdgeMajorant r C M N := by
  obtain ⟨a,ha,hgap⟩ := compact_root_product_disk_of_boundary_gap hb hQ hB hS κ hκ
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hnum⟩ := compact_full_numerator_polydisks hb hQ hB hS
  refine ⟨min a δ,r,C,M,(4/κ+1),lt_min ha hδ,hr,hr1,hC,hM,by positivity,?_⟩
  intro v hv N hN q hq hboundary p hp
  have hu : ‖p-((0:ℂ),v)‖<min a δ/(N:ℝ) := by simpa only [mem_ball,dist_eq_norm] using hp
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hua : ‖p-((0:ℂ),v)‖<a/(N : ℝ) := hu.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) hNp.le)
  have huδ : ‖p-((0:ℂ),v)‖<δ := by
    have hh : min a δ/(N : ℝ)≤min a δ := (div_le_iff₀ hNp).mpr (by nlinarith [lt_min ha hδ])
    exact hu.trans_le (hh.trans (min_le_right _ _))
  obtain ⟨hroot,hprod⟩ := hgap v hv N hN q hq hboundary p (by simpa only [mem_ball,dist_eq_norm] using hua)
  have hnumq := hnum v hv N q hq
  have hpδ : p∈ball ((0:ℂ),v) δ := by simpa only [mem_ball,dist_eq_norm] using huδ
  have hA := hnumq.1 p hpδ
  have hAn : ‖independentNumerator b p (List.ofFn q)‖≤particleEdgeMajorant r C M N := hnumq.2 p hpδ
  have hne : 1-(∏i,independentRoot b p (q i))≠0 := norm_pos_iff.mp ((by positivity : 0<κ/2).trans_le hprod)
  have hP : AnalyticAt ℂ (fun x=>(∏i,independentRoot b x (q i))) p :=
    Finset.univ.analyticAt_fun_prod (fun i _=>hroot i)
  refine ⟨((analyticAt_const.mul hA).mul ((analyticAt_const.sub hP).inv hne)).sub hA,?_⟩
  have hinv : ‖(1-(∏i,independentRoot b p (q i)))⁻¹‖≤2/κ := by
    rw [norm_inv]
    have hh := inv_anti₀ (by positivity : 0<κ/2) hprod
    convert hh using 1
    field_simp
  have hW : 0≤particleEdgeMajorant r C M N :=
    particleEdgeMajorant_nonneg hr.le hC.le hM.le _
  have hm := mul_le_mul hAn hinv (norm_nonneg _) hW
  have hnormF := norm_sub_le
    ((2 : ℂ)*independentNumerator b p (List.ofFn q)*(1-(∏i,independentRoot b p (q i)))⁻¹)
    (independentNumerator b p (List.ofFn q))
  simp only [norm_mul,Complex.norm_ofNat] at hnormF
  change ‖2*independentNumerator b p (List.ofFn q)*(1-(∏i,independentRoot b p (q i)))⁻¹-independentNumerator b p (List.ofFn q)‖≤_
  have heq : (4/κ+1)*particleEdgeMajorant r C M N=
      2*(particleEdgeMajorant r C M N*(2/κ))+particleEdgeMajorant r C M N := by ring
  rw [heq]
  nlinarith only [hnormF,hm,hAn]

end
end IsingBulk.Joint.Negative
