import IsingBulk.Tail.AllBranchExteriorCutoffs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Tail
noncomputable section
open Set Filter IsingBulk.Jets
open scoped ContDiff Topology BigOperators

lemma smoothTransition_jets_bounded (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ k ≤ J, ∀ x : ℝ, ‖iteratedFDeriv ℝ k Real.smoothTransition x‖ ≤ C := by
  have hone (k : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ k Real.smoothTransition x‖ ≤ C := by
    have hc := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_iteratedFDeriv (m := k) (by simp)
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro x
    by_cases hx : x ∈ Icc (-1:ℝ) 2
    · exact (hC x hx).trans (le_max_right _ _)
    · have hout : x < -1 ∨ 2 < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
      have he : ∃ c : ℝ, ‖c‖ ≤ 1 ∧ Real.smoothTransition =ᶠ[𝓝 x] (fun _ => c) := by
        rcases hout with hl|hr
        · refine ⟨0,by norm_num,?_⟩
          filter_upwards [Iio_mem_nhds (show x < 0 by linarith)] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        · refine ⟨1,by norm_num,?_⟩
          filter_upwards [Ioi_mem_nhds (show 1 < x by linarith)] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
      obtain ⟨c,hcnorm,he⟩ := he
      rw [(he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
      by_cases hk0 : k=0
      · subst k
        simpa only [norm_iteratedFDeriv_zero] using hcnorm.trans (le_max_left 1 C)
      · rw [iteratedFDeriv_const_of_ne hk0]
        simp
  induction J with
  | zero =>
    obtain ⟨C,hC,hb⟩ := hone 0
    refine ⟨C,hC,?_⟩
    intro k hk x
    have he : k=0 := by omega
    subst k
    exact hb x
  | succ J ih =>
    obtain ⟨C,hC,hb⟩ := ih
    obtain ⟨D,hD,hd⟩ := hone (J+1)
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro k hk x
    by_cases hkJ : k ≤ J
    · exact (hb k hkJ x).trans (le_max_left _ _)
    · have he : k=J+1 := by omega
      exact (he ▸ hd x).trans (le_max_right _ _)

 def branchMeanCLM (N : ℕ) : (Fin N → ℝ) →L[ℝ] ℝ :=
   (N:ℝ)⁻¹ • ∑ i : Fin N, ContinuousLinearMap.proj (R := ℝ) i

lemma branchMeanCLM_apply (N : ℕ) (u : Fin N → ℝ) : branchMeanCLM N u=branchMean u := by
  simp [branchMeanCLM,branchMean,div_eq_mul_inv,mul_comm]

lemma branchMeanCLM_norm (N : ℕ) : ‖branchMeanCLM N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  by_cases hn : N=0
  · subst N; simp [branchMeanCLM]
  have hnpos : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp only [branchMeanCLM_apply,branchMean,norm_div,Real.norm_eq_abs,abs_of_pos hnpos,one_mul]
  apply (div_le_iff₀ hnpos).mpr
  calc
    _ ≤ ∑ i : Fin N, ‖u i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖u‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm u i)
    _ = _ := by simp [mul_comm]

 def branchCenteredCLM {N : ℕ} (i : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
   ContinuousLinearMap.proj (R := ℝ) i - branchMeanCLM N

lemma branchCenteredCLM_norm {N : ℕ} (i : Fin N) : ‖branchCenteredCLM i‖ ≤ 2 := by
  apply (norm_sub_le _ _).trans
  have hp : ‖ContinuousLinearMap.proj (R := ℝ) i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun (u : Fin N → ℝ) => by simpa using norm_le_pi_norm u i)
  linarith [branchMeanCLM_norm N]

lemma real_squared_linear_jet_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => (L y)^2) x‖ ≤
      ((2).descFactorial k : ℝ)*‖L x‖^(2-k)*‖L‖^k := by
  have he := L.iteratedFDeriv_comp_right (contDiff_id.pow 2) x (i := k) (n := ∞) (by simp)
  change iteratedFDeriv ℝ k (fun y => (L y)^2) x = _ at he
  rw [he]
  have hh := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k (fun z : ℝ => z^2) (L x)) (fun _ : Fin k => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  apply hh.trans_eq
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_pow,norm_mul,norm_pow]
  simp

lemma branchShapeSquare_jet_bound {N : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (u : Fin N → ℝ) (hu : ∀ i, |u i| ≤ R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (@branchShapeSquare N) u‖ ≤ 8*N*(1+R)^2 := by
  have hnu : ‖u‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (fun i => hu i)
  have hx (i : Fin N) : ‖branchCenteredCLM i u‖ ≤ 2*R :=
    ((branchCenteredCLM i).le_opNorm u).trans
      (mul_le_mul (branchCenteredCLM_norm i) hnu (norm_nonneg _) (by norm_num))
  have he : @branchShapeSquare N = fun x => ∑ i : Fin N, (branchCenteredCLM i x)^2 := by
    funext x; simp [branchShapeSquare,branchCenteredCLM,branchMeanCLM_apply]
  rw [he,iteratedFDeriv_fun_sum_apply (fun i _ =>
    (((branchCenteredCLM i).contDiff.pow 2 : ContDiff ℝ ∞ _).of_le (by simp)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin N, 8*(1+R)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := real_squared_linear_jet_norm (branchCenteredCLM i) u k
      have hL := branchCenteredCLM_norm i
      rcases k with _|_|_|k
      · have hs := pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
        simp only [Real.norm_eq_abs,sq_abs] at hs
        norm_num at hh ⊢
        nlinarith [sq_nonneg R]
      · norm_num at hh ⊢
        have hm := mul_le_mul (hx i) hL (norm_nonneg _) (by positivity : 0 ≤ 2*R)
        simp only [Real.norm_eq_abs] at hm
        nlinarith [sq_nonneg R]
      · norm_num at hh ⊢; nlinarith [norm_nonneg (branchCenteredCLM i),sq_nonneg R]
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),Nat.cast_zero,zero_mul,zero_mul] at hh
        exact hh.trans (by positivity)
    _ = _ := by simp; ring

def branchShapeJetCost (N : ℕ) (R rho : ℝ) : ℝ :=
  1+8*N*(1+R)^2/(3*rho^2)

lemma branchShapeJetCost_ge_one (N : ℕ) (R rho : ℝ) : 1 ≤ branchShapeJetCost N R rho := by
  unfold branchShapeJetCost
  have hh : 0 ≤ 8*(N:ℝ)*(1+R)^2/(3*rho^2) := by positivity
  linarith

lemma scaled_branchShapeSquare_positive_jet {N : ℕ} (R rho : ℝ)
    (hR : 0 ≤ R) (hr : 0 < rho) (u : Fin N → ℝ) (hu : ∀ i, |u i| ≤ R)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (fun v : Fin N → ℝ =>
      (branchShapeSquare v-rho^2)/(4*rho^2-rho^2)) u‖ ≤ (branchShapeJetCost N R rho)^k := by
  have hshape := branchShapeSquare_smooth N
  have he : (fun v : Fin N → ℝ => (branchShapeSquare v-rho^2)/(4*rho^2-rho^2)) =
      (fun v => (3*rho^2)⁻¹ • (branchShapeSquare v-rho^2)) := by funext v; simp only [smul_eq_mul]; ring
  rw [he,iteratedFDeriv_const_smul_apply' ((hshape.sub contDiff_const).of_le (by simp)).contDiffAt,
    fun_iteratedFDeriv_sub_apply (hshape.of_le (by simp)).contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : k≠0),Pi.zero_apply,sub_zero,norm_smul]
  have hscale : ‖(3*rho^2)⁻¹‖ = (3*rho^2)⁻¹ := abs_of_pos (by positivity)
  rw [hscale]
  calc
    _ ≤ (3*rho^2)⁻¹*(8*N*(1+R)^2) :=
      mul_le_mul_of_nonneg_left (branchShapeSquare_jet_bound R hR u hu k) (by positivity)
    _ ≤ branchShapeJetCost N R rho := by unfold branchShapeJetCost; simp only [div_eq_mul_inv]; nlinarith
    _ ≤ (branchShapeJetCost N R rho)^k :=
      le_self_pow₀ (branchShapeJetCost_ge_one N R rho) (by omega)

lemma real_cutoffJet_fderiv_norm {N : ℕ} (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (u : Fin N → ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (cutoffJet l f) u‖ ≤ ‖iteratedFDeriv ℝ (k+l.length) f u‖ := by
  induction l generalizing k with
  | nil => simp [cutoffJet]
  | cons i l ih =>
    have hs := cutoffJet_contDiff l f hf
    have hh := norm_iteratedFDeriv_clm_apply_const (c := Pi.single i (1:ℝ)) (n := k) (x := u)
      (N := ∞) ((hs.fderiv_right (by simp)).contDiffAt) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at hh
    have he : ‖(Pi.single i (1:ℝ) : Fin N → ℝ)‖ = 1 := by
      rw [Pi.norm_single]
      norm_num
    rw [he,one_mul] at hh
    apply hh.trans
    have hh2 := ih (k+1)
    rw [show k+1+l.length=k+(l.length+1) by omega] at hh2
    exact hh2

/-- Explicit polynomial-N and inverse-scale cost; constants depend only on J. -/
theorem branch_shape_cutoff_jet_bounds (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (N : ℕ) (R rho : ℝ), 0 ≤ R → 0 < rho →
      ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ R) → ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (branchFarCutoff rho) u‖ ≤ J.factorial*C*(branchShapeJetCost N R rho)^J ∧
      ‖cutoffJet l (branchNearCutoff rho) u‖ ≤ 1+J.factorial*C*(branchShapeJetCost N R rho)^J := by
  obtain ⟨C,hC,hCb⟩ := smoothTransition_jets_bounded J
  refine ⟨C,hC,?_⟩
  intro N R rho hR hr u hu l hl
  have hfar (k : ℕ) (hk : k ≤ J) :
      ‖iteratedFDeriv ℝ k (@branchFarCutoff N rho) u‖ ≤ J.factorial*C*(branchShapeJetCost N R rho)^J := by
    let F : (Fin N → ℝ) → ℝ := fun v => (branchShapeSquare v-rho^2)/(4*rho^2-rho^2)
    have hF : ContDiff ℝ ∞ F := ((branchShapeSquare_smooth N).sub contDiff_const).div_const _
    have hh := norm_iteratedFDeriv_comp_le
      (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition) hF (by simp : (k:ℕ∞ω) ≤ ∞)
      u (C := C) (D := branchShapeJetCost N R rho)
      (fun i hi => hCb i (hi.trans hk) (F u))
      (fun i hi _ => scaled_branchShapeSquare_positive_jet R rho hR hr u hu i hi)
    apply hh.trans
    have hcost := branchShapeJetCost_ge_one N R rho
    gcongr
  have hnear (k : ℕ) (hk : k ≤ J) :
      ‖iteratedFDeriv ℝ k (@branchNearCutoff N rho) u‖ ≤ 1+J.factorial*C*(branchShapeJetCost N R rho)^J := by
    unfold branchNearCutoff
    rw [fun_iteratedFDeriv_sub_apply contDiffAt_const
      (((branch_shape_cutoffs_smooth rho).1.of_le (by simp)).contDiffAt)]
    apply (norm_sub_le _ _).trans (add_le_add _ (hfar k hk))
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  constructor
  · have hh := real_cutoffJet_fderiv_norm l (branchFarCutoff rho) (branch_shape_cutoffs_smooth rho).1 u 0
    rw [Nat.zero_add] at hh
    apply (show ‖cutoffJet l (branchFarCutoff rho) u‖ ≤ ‖iteratedFDeriv ℝ l.length (branchFarCutoff rho) u‖ from by simpa using hh).trans
    exact hfar l.length hl
  · have hh := real_cutoffJet_fderiv_norm l (branchNearCutoff rho) (branch_shape_cutoffs_smooth rho).2 u 0
    rw [Nat.zero_add] at hh
    apply (show ‖cutoffJet l (branchNearCutoff rho) u‖ ≤ ‖iteratedFDeriv ℝ l.length (branchNearCutoff rho) u‖ from by simpa using hh).trans
    exact hnear l.length hl

end
end IsingBulk.Tail
