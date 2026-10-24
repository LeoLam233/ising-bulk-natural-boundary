import IsingBulk.Anisotropic.NegativeDominance.BoundaryGapDisk
import IsingBulk.Anisotropic.RegularEdges.ParticleMajorant
import IsingBulk.Anisotropic.RegularEdges.IntegrandJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- A proved boundary gap controls the actual complete integrand on a/N,
with the full particle majorant and all one-body and pair factors retained. -/
theorem fullIntegrand_disk_of_boundary_gap {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (κ : ℝ) (hκ : 0<κ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      κ≤‖1-edgeRootProduct b B 0 q‖ → ∀u : ℂ,‖u‖<a/(N : ℝ) →
      AnalyticAt ℂ (fun w=>edgeFullIntegrand b B S w q) u ∧
        ‖edgeFullIntegrand b B S u q‖≤K*particleEdgeMajorant r C M N := by
  obtain ⟨a,ha,hgap⟩ := edgeRootProduct_disk_of_boundary_gap hb hB hBa κ hκ
  obtain ⟨δ,r,C,M,K,hδ,hr,hr1,hC,hM,hK,hnum⟩ := edgeNumerator_all_jets hb hB hBa hSa hS0 0
  refine ⟨min a δ,r,C,M,(4/κ+1)*K,lt_min ha hδ,hr,hr1,hC,hM,by positivity,?_⟩
  intro N hN q hq hboundary u hu
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hua : ‖u‖<a/(N : ℝ) := hu.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) hNp.le)
  have huδ : ‖u‖<δ := by
    have hh : min a δ/(N : ℝ)≤min a δ := (div_le_iff₀ hNp).mpr (by nlinarith [lt_min ha hδ])
    exact hu.trans_le (hh.trans (min_le_right _ _))
  obtain ⟨hroot,hprod⟩ := hgap N hN q hq hboundary u hua
  obtain ⟨hA,hAj⟩ := hnum u huδ N q hq
  have hAn : ‖edgeNumerator b B S u (List.ofFn q)‖≤K*particleEdgeMajorant r C M N := by
    simpa using hAj 0 le_rfl
  have hne : 1-edgeRootProduct b B u q≠0 := norm_pos_iff.mp ((by positivity : 0<κ/2).trans_le hprod)
  have hP : AnalyticAt ℂ (fun w=>edgeRootProduct b B w q) u :=
    Finset.univ.analyticAt_fun_prod (fun i _=>hroot i)
  refine ⟨((analyticAt_const.mul hA).mul ((analyticAt_const.sub hP).inv hne)).sub hA,?_⟩
  have hinv : ‖(1-edgeRootProduct b B u q)⁻¹‖≤2/κ := by
    rw [norm_inv]
    have hh := inv_anti₀ (by positivity : 0<κ/2) hprod
    convert hh using 1
    field_simp
  have hW : 0≤K*particleEdgeMajorant r C M N :=
    mul_nonneg hK.le (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)
  have hm := mul_le_mul hAn hinv (norm_nonneg _) hW
  have hnormF := norm_sub_le
    ((2 : ℂ)*edgeNumerator b B S u (List.ofFn q)*(1-edgeRootProduct b B u q)⁻¹)
    (edgeNumerator b B S u (List.ofFn q))
  simp only [norm_mul,Complex.norm_ofNat] at hnormF
  change ‖2*edgeNumerator b B S u (List.ofFn q)*(1-edgeRootProduct b B u q)⁻¹-edgeNumerator b B S u (List.ofFn q)‖≤_
  have heq : (4/κ+1)*K*particleEdgeMajorant r C M N=
      2*(K*particleEdgeMajorant r C M N*(2/κ))+K*particleEdgeMajorant r C M N := by ring
  rw [heq]
  nlinarith only [hnormF,hm,hAn]

end
end IsingBulk.Anisotropic.NegativeDominance
