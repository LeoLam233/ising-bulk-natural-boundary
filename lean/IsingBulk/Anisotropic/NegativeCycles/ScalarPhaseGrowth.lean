import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarQuadraticControl

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric Filter NegativeNormalForm
open scoped Topology BigOperators

theorem negativePhase_uniform_growth (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ t v : ℂ, ‖t‖<r → ‖v‖<r →
      ‖negativePhase B phi hphi t v-(phi:ℂ)*Complex.I‖≤C*‖t‖+C*‖v‖^2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (0,0) := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  let S : ScalarTriple → ℂ := fun p => negativePhase B phi hphi p.1 (p.2.1+p.2.2)
  have hS : AnalyticAt ℂ S 0 := hg.fun_comp_of_eq
    (f := fun p : ScalarTriple => (p.1,p.2.1+p.2.2))
    (analyticAt_fst.prod ((analyticAt_fst.comp analyticAt_snd).add
      (analyticAt_snd.comp analyticAt_snd))) (by simp)
  obtain ⟨a,L,ha,hL,hquad⟩ := analytic_even_axis_quadratic_control S hS (by
    intro t v
    simpa only [S,zero_add] using negativePhase_even B phi hphi t v)
  obtain ⟨b,M,K,hb,hM,_hK,_hbound,hLip⟩ := analytic_scalarTriple_uniform_lipschitz hS
  have hcenter : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_center B phi hphi 0
  refine ⟨min a b,L+M,lt_min ha hb,by linarith,?_⟩
  intro t v ht hv
  have hpa : ‖(t,((0:ℂ),v))‖<a := max_lt (ht.trans_le (min_le_left _ _))
    (max_lt (by simpa using ha) (hv.trans_le (min_le_left _ _)))
  have hpb : ‖(t,((0:ℂ),(0:ℂ)))‖<b := max_lt (ht.trans_le (min_le_right _ _))
    (by simpa using hb)
  have h1 := hquad (t,(0,v)) hpa
  simp only [S,zero_add,norm_zero,add_zero,mul_assoc,← pow_two] at h1
  have h2 := hLip (t,(0,0)) 0 hpb (by simpa using hb)
  simp only [S,zero_add,Prod.fst_zero,Prod.snd_zero,hcenter,sub_zero,Prod.norm_def,
    norm_zero,max_self,max_eq_left (norm_nonneg _)] at h2
  have hh := norm_add_le (negativePhase B phi hphi t v-negativePhase B phi hphi t 0)
    (negativePhase B phi hphi t 0-(phi:ℂ)*Complex.I)
  rw [sub_add_sub_cancel] at hh
  nlinarith [norm_nonneg t,sq_nonneg ‖v‖]

theorem poleEquation_uniform_growth {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (r C : ℝ)
    (h : ∀ t v : ℂ, ‖t‖<r → ‖v‖<r →
      ‖negativePhase B phi hphi t v-(phi:ℂ)*Complex.I‖≤C*‖t‖+C*‖v‖^2)
    (t : ℂ) (v : Config n) (ht : ‖t‖<r) (hv : ∀ i, ‖v i‖<r) :
    ‖poleEquation B phi hphi 0 t v‖≤(n:ℝ)*C*‖t‖+C*absoluteEnergy v := by
  unfold poleEquation
  simp only [zero_add]
  calc
    _ ≤ ∑ i, ‖negativePhase B phi hphi t (v i)-(phi:ℂ)*Complex.I‖ := norm_sum_le _ _
    _ ≤ ∑ i, (C*‖t‖+C*‖v i‖^2) := Finset.sum_le_sum fun i _ => h t (v i) ht (hv i)
    _ = _ := by simp only [absoluteEnergy,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]; ring

end
end IsingBulk.Anisotropic.NegativeCycles
