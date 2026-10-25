import IsingBulk.Joint.Negative.FamilyRootGap
import IsingBulk.Joint.RegularEdges.CompactFullJets

/-! # Full odd resolvent control on common polynomial-scale polydisks -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Joint.RegularEdges Set Metric
open scoped Topology BigOperators

/-- Full, not numerator-only, uniform control on all odd constrained tori. -/
theorem compact_odd_full_integrand_control {b : ℝ} {Q : Set (ℂ × ℂ)}
    (hb : |b|<1) (hQ : IsCompact Q)
    (hB : ∀ v∈Q, 0<v.1.im) (hS : ∀ v∈Q, v.2≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ w∈Q, ∀ n : ℕ, Odd (n+1) → ∀ v : Fin n→ℝ,
      ∀ p∈ball ((0:ℂ),w) (a/((n+1:ℕ):ℝ)^3),
        AnalyticAt ℂ (fun x => independentFullIntegrand b x (negativeShiftedAngles n v)) p ∧
        ‖independentFullIntegrand b p (negativeShiftedAngles n v)‖≤
          K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1) := by
  obtain ⟨a,c,ha,hc,hgap⟩ := compact_odd_complex_product_gap hb hQ hB hS
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hnum⟩ := compact_full_numerator_polydisks hb hQ hB hS
  refine ⟨min a δ,r,C,M,3/c,lt_min ha hδ,hr,hr1,hC,hM,by positivity,?_⟩
  intro w hw n hn v p hp
  have hu : ‖p-((0:ℂ),w)‖<min a δ/((n+1:ℕ):ℝ)^3 := by simpa only [mem_ball,dist_eq_norm] using hp
  let N : ℝ := (n+1 : ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hua : ‖p-((0:ℂ),w)‖<a/N^3 := hu.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have huδ : ‖p-((0:ℂ),w)‖<δ := by
    have hh : min a δ/N^3≤min a δ := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith [lt_min ha hδ])
    exact hu.trans_le (hh.trans (min_le_right _ _))
  let q := negativeShiftedAngles n v
  have hq (i : Fin (n+1)) : q i∈Icc (-Real.pi) Real.pi := wrapAngle_mem _
  obtain ⟨hroot,hprod⟩ := hgap w hw n hn v p (by simpa only [mem_ball,dist_eq_norm] using hua)
  have hnumq := hnum w hw (n+1) q hq
  have hpδ : p∈ball ((0:ℂ),w) δ := by simpa only [mem_ball,dist_eq_norm] using huδ
  have hA := hnumq.1 p hpδ
  have hAn : ‖independentNumerator b p (List.ofFn q)‖≤particleEdgeMajorant r C M (n+1) := hnumq.2 p hpδ
  let P := ∏ i,independentRoot b p (q i)
  have hd : 0<c/N^2 := by positivity
  have hd1 : c/N^2≤1 := hprod.trans (sub_le_self _ (norm_nonneg _))
  have hnorm : c/N^2≤‖1-P‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) P
    rw [norm_one] at hh
    exact hprod.trans hh
  have hne : 1-P≠0 := norm_pos_iff.mp (hd.trans_le hnorm)
  have hP : AnalyticAt ℂ (fun x => ∏ i,independentRoot b x (q i)) p :=
    Finset.univ.analyticAt_fun_prod (fun i _ => hroot i)
  refine ⟨?_,?_⟩
  · exact ((analyticAt_const.mul hA).mul ((analyticAt_const.sub hP).inv hne)).sub hA
  have hinv : ‖(1-P)⁻¹‖≤N^2/c := by
    rw [norm_inv]
    have hh := inv_anti₀ hd hnorm
    convert hh using 1; field_simp
  have hW : 0≤particleEdgeMajorant r C M (n+1) :=
    particleEdgeMajorant_nonneg hr.le hC.le hM.le _
  have hfrac : 1≤N^2/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_one (pow_pos hN0 2)).mp hd1
    simpa only [one_mul] using hh
  have hm := mul_le_mul hAn hinv (norm_nonneg _) hW
  have hWle := mul_le_mul_of_nonneg_left hfrac hW
  have hnormF := norm_sub_le ((2 : ℂ)*independentNumerator b p (List.ofFn q)*(1-P)⁻¹)
    (independentNumerator b p (List.ofFn q))
  simp only [norm_mul,Complex.norm_ofNat] at hnormF
  change ‖2*independentNumerator b p (List.ofFn q)*(1-P)⁻¹-independentNumerator b p (List.ofFn q)‖≤_
  have heq : (3/c)*N^2*particleEdgeMajorant r C M (n+1)=
      3*(particleEdgeMajorant r C M (n+1))*(N^2/c) := by ring
  change _≤(3/c)*N^2*particleEdgeMajorant r C M (n+1)
  rw [heq]
  nlinarith

end
end IsingBulk.Joint.Negative
