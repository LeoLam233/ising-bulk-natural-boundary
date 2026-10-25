import IsingBulk.Joint.Negative.FamilyQuadratic
import IsingBulk.Anisotropic.NegativeNormalForm.ComplexPeriodLoss

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_hessian_quadratic (B : ℂ × E→ℂ) (phi : ℝ)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀d : ℂ,‖d‖<r →
      ‖centralHessian (familyMember B eta) phi d-1‖≤L*‖d‖^2 ∧
      ‖centralHessian (familyMember B eta) phi d-1‖<1/2 := by
  obtain ⟨a,L,ha,hL,hquad⟩ := compact_family_even_quadratic
    (fun q : ScalarTriple × E=>centralHessian (familyMember B q.2) phi q.1.2.2) hP
    (fun eta heta=>(family_hessian_analyticAt B phi eta (hB eta heta)).comp_of_eq
      (f:=fun q : ScalarTriple × E=>(q.1.2.2,q.2))
      ((analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)).prod analyticAt_snd) rfl)
    (fun eta _ _ v=>centralHessian_even (familyMember B eta) phi v)
  let r := min a (min 1 (1/(4*(L+1))))
  have hr : 0<r := lt_min ha (lt_min zero_lt_one (by positivity))
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta d hd
  have hqa := hquad eta heta (0,(0,d)) (by simpa using hd.trans_le (min_le_left _ _))
  simp only [norm_zero,zero_add,centralHessian_zero] at hqa
  have hq : ‖centralHessian (familyMember B eta) phi d-1‖≤L*‖d‖^2 := by
    nlinarith [hqa]
  refine ⟨hq,?_⟩
  have hd1 : ‖d‖<1 := hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hds : ‖d‖<1/(4*(L+1)) := hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hm := (lt_div_iff₀ (by positivity : 0<4*(L+1))).mp hds
  have hsq : ‖d‖^2≤‖d‖ := by nlinarith [norm_nonneg d]
  nlinarith [mul_le_mul_of_nonneg_left hsq hL.le,norm_nonneg d]

theorem compact_family_hessian_period_loss (B : ℂ × E→ℂ) (phi : ℝ) {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀eta∈P,∀ n : ℕ, 3≤n → ∀ d : ℂ, ‖d‖<r →
      (1:ℝ)/2≤(centralHessian (familyMember B eta) phi d).re ∧
      (‖centralHessian (familyMember B eta) phi d‖/(centralHessian (familyMember B eta) phi d).re)^(alpha n)≤
        Real.exp (L^2*(n:ℝ)^2*‖d‖^4) := by
  obtain ⟨r,L,hr,hL,hbound⟩ := compact_family_hessian_quadratic B phi hP hB
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta n hn d hd
  obtain ⟨hq,hnear⟩ := hbound eta heta d hd
  have hre : (1:ℝ)/2≤(centralHessian (familyMember B eta) phi d).re := by
    have hh := Complex.re_le_norm (1-centralHessian (familyMember B eta) phi d)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re,Complex.one_re] at hh
    linarith
  refine ⟨hre,?_⟩
  have hpow := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith))
    (complex_norm_re_ratio_le_exp _ hre) (alpha n)
  rw [←Real.exp_nat_mul] at hpow
  have hsq : ‖centralHessian (familyMember B eta) phi d-1‖^2≤L^2*‖d‖^4 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hq 2
    nlinarith
  have han := (alpha_pos_and_twice_le n hn).2
  have hanR : 2*(alpha n:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (show 2*alpha n≤n^2 by simpa [pow_two] using han)
  apply hpow.trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (n:ℝ)^2*‖centralHessian (familyMember B eta) phi d-1‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hanR (sq_nonneg ‖centralHessian (familyMember B eta) phi d-1‖)]
    _ ≤ (n:ℝ)^2*(L^2*‖d‖^4) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

end
end IsingBulk.Joint.Negative
