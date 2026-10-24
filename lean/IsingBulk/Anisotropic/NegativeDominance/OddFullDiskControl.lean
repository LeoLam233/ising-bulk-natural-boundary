import IsingBulk.Anisotropic.NegativeDominance.OddComplexGap
import IsingBulk.Anisotropic.RegularEdges.ParticleMajorant

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- Full, not numerator-only, analytic control on a polynomial particle-scale
complex disk. This includes every odd constrained angular configuration. -/
theorem odd_negative_fullIntegrand_complex_control {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ, ∀ u : ℂ,
      ‖u‖<a/((n+1 : ℕ) : ℝ)^3 →
        AnalyticAt ℂ (fun w => negativeShiftedFullIntegrand b B S n w v) u ∧
        ‖negativeShiftedFullIntegrand b B S n u v‖≤
          K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1) := by
  obtain ⟨a,c,ha,hc,hgap⟩ := odd_negative_complex_product_gap hb hB hBa
  obtain ⟨δ,r,C,M,K,hδ,hr,hr1,hC,hM,hK,hnum⟩ := edgeNumerator_all_jets hb hB hBa hSa hS0 0
  refine ⟨min a δ,r,C,M,3*K/c,lt_min ha hδ,hr,hr1,hC,hM,by positivity,?_⟩
  intro n hn v u hu
  let N : ℝ := (n+1 : ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hua : ‖u‖<a/N^3 := hu.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have huδ : ‖u‖<δ := by
    have hh : min a δ/N^3≤min a δ := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith [lt_min ha hδ])
    exact hu.trans_le (hh.trans (min_le_right _ _))
  let q := negativeShiftedAngles n v
  have hq (i : Fin (n+1)) : q i∈Icc (-Real.pi) Real.pi := wrapAngle_mem _
  obtain ⟨hroot,hprod⟩ := hgap n hn v u hua
  obtain ⟨hA,hAj⟩ := hnum u huδ (n+1) q hq
  have hAn : ‖edgeNumerator b B S u (List.ofFn q)‖≤K*particleEdgeMajorant r C M (n+1) := by
    simpa using hAj 0 le_rfl
  let P := edgeRootProduct b B u q
  have hd : 0<c/N^2 := by positivity
  have hd1 : c/N^2≤1 := hprod.trans (sub_le_self _ (norm_nonneg _))
  have hnorm : c/N^2≤‖1-P‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) P
    rw [norm_one] at hh
    exact hprod.trans hh
  have hne : 1-P≠0 := norm_pos_iff.mp (hd.trans_le hnorm)
  have hP : AnalyticAt ℂ (fun w => edgeRootProduct b B w q) u :=
    Finset.univ.analyticAt_fun_prod (fun i _ => hroot i)
  refine ⟨?_,?_⟩
  · exact ((analyticAt_const.mul hA).mul ((analyticAt_const.sub hP).inv hne)).sub hA
  have hinv : ‖(1-P)⁻¹‖≤N^2/c := by
    rw [norm_inv]
    have hh := inv_anti₀ hd hnorm
    convert hh using 1; field_simp
  have hW : 0≤K*particleEdgeMajorant r C M (n+1) :=
    mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)
  have hfrac : 1≤N^2/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_one (pow_pos hN0 2)).mp hd1
    simpa only [one_mul] using hh
  have hm := mul_le_mul hAn hinv (norm_nonneg _) hW
  have hWle := mul_le_mul_of_nonneg_left hfrac hW
  have hnormF := norm_sub_le ((2 : ℂ)*edgeNumerator b B S u (List.ofFn q)*(1-P)⁻¹)
    (edgeNumerator b B S u (List.ofFn q))
  simp only [norm_mul,Complex.norm_ofNat] at hnormF
  change ‖2*edgeNumerator b B S u (List.ofFn q)*(1-P)⁻¹-edgeNumerator b B S u (List.ofFn q)‖≤_
  have heq : (3*K/c)*N^2*particleEdgeMajorant r C M (n+1)=
      3*(K*particleEdgeMajorant r C M (n+1))*(N^2/c) := by ring
  change _≤(3*K/c)*N^2*particleEdgeMajorant r C M (n+1)
  rw [heq]
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
