import IsingBulk.Tail.ShapeCutoffJets

namespace IsingBulk.Tail
noncomputable section
open Set Filter IsingBulk.Jets
open scoped ContDiff Topology BigOperators

def normalizedShapeCLM (N : ℕ) (rho : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun i => rho⁻¹ • branchCenteredCLM i)

lemma normalizedShapeCLM_apply {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) (i : Fin N) :
    normalizedShapeCLM N rho u i = (u i-branchMean u)/rho := by
  simp [normalizedShapeCLM,branchCenteredCLM,branchMeanCLM_apply,div_eq_mul_inv,mul_comm]

lemma branchMean_normalizedShape {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) :
    branchMean (normalizedShapeCLM N rho u)=0 := by
  by_cases hN : N=0
  · subst N; simp [branchMean]
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  change (∑ i, normalizedShapeCLM N rho u i)/(N:ℝ)=0
  simp only [normalizedShapeCLM_apply]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  simp [branchMean,hN0]
  left
  field_simp
  ring

lemma branchShapeSquare_normalizedShape {N : ℕ} (rho : ℝ) (u : Fin N → ℝ) :
    branchShapeSquare (normalizedShapeCLM N rho u)=branchShapeSquare u/rho^2 := by
  simp only [branchShapeSquare,branchMean_normalizedShape,sub_zero,normalizedShapeCLM_apply,div_pow,Finset.sum_div]

lemma branchFarCutoff_normalized {N : ℕ} (rho : ℝ) (hr : 0 < rho) :
    @branchFarCutoff N rho = (@branchFarCutoff N 1) ∘ normalizedShapeCLM N rho := by
  funext u
  simp only [Function.comp_apply,branchFarCutoff,thresholdStep,branchShapeSquare_normalizedShape]
  congr 1
  field_simp

lemma normalizedShapeCLM_norm {N : ℕ} (rho : ℝ) (hr : 0 < rho) :
    ‖normalizedShapeCLM N rho‖ ≤ 2/rho := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [normalizedShapeCLM_apply,norm_div,Real.norm_eq_abs,abs_of_pos hr]
  have hh := ((branchCenteredCLM i).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (branchCenteredCLM_norm i) (norm_nonneg u))
  have he : branchCenteredCLM i u=u i-branchMean u := by simp [branchCenteredCLM,branchMeanCLM_apply]
  rw [he] at hh
  calc
    _ ≤ (2*‖u‖)/rho := div_le_div_of_nonneg_right hh hr.le
    _ = _ := by ring

lemma normalizedShape_point_bound {N : ℕ} (rho : ℝ) (hr : 0 < rho)
    (u : Fin N → ℝ) (hu : branchShapeRadius u ≤ 2*rho) :
    ∀ i, |normalizedShapeCLM N rho u i| ≤ 2 := by
  intro i
  rw [normalizedShapeCLM_apply,abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).mpr ((deviation_le_branchShapeRadius u i).trans hu)

lemma branchFarCutoff_fixed_fderiv_bound (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ N : ℕ, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ 2) → ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (@branchFarCutoff N 1) u‖ ≤ J.factorial*C*(1+24*N)^J := by
  obtain ⟨C,hC,hCb⟩ := smoothTransition_jets_bounded J
  refine ⟨C,hC,?_⟩
  intro N u hu k hk
  let F : (Fin N → ℝ) → ℝ := fun v => (branchShapeSquare v-(1:ℝ)^2)/(4*(1:ℝ)^2-(1:ℝ)^2)
  have hF : ContDiff ℝ ∞ F := ((branchShapeSquare_smooth N).sub contDiff_const).div_const _
  have hh := norm_iteratedFDeriv_comp_le
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition) hF (by simp : (k:ℕ∞ω) ≤ ∞)
    u (C := C) (D := branchShapeJetCost N 2 1)
    (fun i hi => hCb i (hi.trans hk) (F u))
    (fun i hi _ => scaled_branchShapeSquare_positive_jet 2 1 (by norm_num) (by norm_num) u hu i hi)
  have hd : branchShapeJetCost N 2 1=1+24*N := by unfold branchShapeJetCost; norm_num; ring
  rw [hd] at hh
  have hbase : (1:ℝ) ≤ 1+24*N := by
    have : (0:ℝ) ≤ 24*N := by positivity
    linarith
  exact hh.trans (by gcongr)

/-- One inverse-radius power per real derivative, including near equality. -/
theorem branch_shape_cutoff_sharp_fderiv (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (N : ℕ) (rho : ℝ), 0 < rho → ∀ u : Fin N → ℝ, ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (@branchFarCutoff N rho) u‖ ≤
        C*(1+24*N)^J*(rho⁻¹)^k ∧
      ‖iteratedFDeriv ℝ k (@branchNearCutoff N rho) u‖ ≤
        C*(1+24*N)^J*(rho⁻¹)^k := by
  obtain ⟨C,hC,hbase⟩ := branchFarCutoff_fixed_fderiv_bound J
  let B := (2:ℝ)^J*J.factorial*C
  have hB : 1 ≤ B := by
    dsimp [B]
    have hp : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    have hf : (1:ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_pos J
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hf) hC
  refine ⟨B,hB,?_⟩
  intro N rho hr u k hk
  have hcost : 1 ≤ (1+24*(N:ℝ))^J := one_le_pow₀ (by
    have : 0 ≤ 24*(N:ℝ) := by positivity
    linarith)
  have hpos : 0 ≤ B*(1+24*(N:ℝ))^J*(rho⁻¹)^k := by positivity
  by_cases hk0 : k=0
  · subst k
    have hrange := thresholdStep_range (rho^2) (4*rho^2) (branchShapeSquare u)
    have hbnd : 1 ≤ B*(1+24*(N:ℝ))^J := by nlinarith
    constructor
    · simpa only [norm_iteratedFDeriv_zero,branchFarCutoff,Real.norm_eq_abs,
        abs_of_nonneg hrange.1,pow_zero,mul_one] using hrange.2.trans hbnd
    · have hn : 0 ≤ 1-thresholdStep (rho^2) (4*rho^2) (branchShapeSquare u) := by linarith
      simpa only [norm_iteratedFDeriv_zero,branchNearCutoff,branchFarCutoff,Real.norm_eq_abs,
        abs_of_nonneg hn,pow_zero,mul_one] using (show 1-thresholdStep (rho^2) (4*rho^2) (branchShapeSquare u) ≤ B*(1+24*(N:ℝ))^J by linarith)
  have hfar : ‖iteratedFDeriv ℝ k (@branchFarCutoff N rho) u‖ ≤
      B*(1+24*N)^J*(rho⁻¹)^k := by
    by_cases hu : branchShapeRadius u ≤ 2*rho
    · let L := normalizedShapeCLM N rho
      rw [branchFarCutoff_normalized rho hr]
      have he := L.iteratedFDeriv_comp_right (branch_shape_cutoffs_smooth (N := N) 1).1 u
        (i := k) (n := ∞) (by simp)
      rw [he]
      have hh := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ k (@branchFarCutoff N 1) (L u)) (fun _ : Fin k => L)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
      calc
        _ ≤ ‖iteratedFDeriv ℝ k (@branchFarCutoff N 1) (L u)‖*‖L‖^k := hh
        _ ≤ (J.factorial*C*(1+24*N)^J)*(2/rho)^k := by
          apply mul_le_mul (hbase N (L u) (normalizedShape_point_bound rho hr u hu) k hk)
            (pow_le_pow_left₀ (norm_nonneg _) (normalizedShapeCLM_norm rho hr) k)
            (by positivity) (by positivity)
        _ ≤ B*(1+24*N)^J*(rho⁻¹)^k := by
          rw [div_eq_mul_inv,mul_pow]
          dsimp [B]
          have hp : (2:ℝ)^k ≤ 2^J := pow_le_pow_right₀ (by norm_num) hk
          nlinarith [mul_le_mul_of_nonneg_right hp
            (show 0 ≤ J.factorial*C*(1+24*(N:ℝ))^J*(rho⁻¹)^k by positivity)]
    · have hc : Continuous (@branchShapeRadius N) := by unfold branchShapeRadius branchMean; fun_prop
      have he : (@branchFarCutoff N rho) =ᶠ[𝓝 u] (fun _ => (1:ℝ)) := by
        filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds (lt_of_not_ge hu))] with v hv
        apply thresholdStep_one (by nlinarith [sq_pos_of_pos hr])
        rw [branchShapeSquare_eq]
        nlinarith
      rw [(he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds,iteratedFDeriv_const_of_ne hk0]
      simpa using hpos
  refine ⟨hfar,?_⟩
  unfold branchNearCutoff
  rw [fun_iteratedFDeriv_sub_apply contDiffAt_const
    (((branch_shape_cutoffs_smooth rho).1.of_le (by simp)).contDiffAt),
    iteratedFDeriv_const_of_ne hk0,Pi.zero_apply,zero_sub,norm_neg]
  exact hfar

theorem branch_shape_cutoff_sharp_words (J : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (N : ℕ) (rho : ℝ), 0 < rho → ∀ u : Fin N → ℝ, ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (branchFarCutoff rho) u‖ ≤ C*(1+24*N)^J*(rho⁻¹)^l.length ∧
      ‖cutoffJet l (branchNearCutoff rho) u‖ ≤ C*(1+24*N)^J*(rho⁻¹)^l.length := by
  obtain ⟨C,hC,hb⟩ := branch_shape_cutoff_sharp_fderiv J
  refine ⟨C,hC,?_⟩
  intro N rho hr u l hl
  have hfar := real_cutoffJet_fderiv_norm l (branchFarCutoff rho) (branch_shape_cutoffs_smooth rho).1 u 0
  have hnear := real_cutoffJet_fderiv_norm l (branchNearCutoff rho) (branch_shape_cutoffs_smooth rho).2 u 0
  rw [Nat.zero_add] at hfar hnear
  simp only [norm_iteratedFDeriv_zero] at hfar hnear
  exact ⟨hfar.trans (hb N rho hr u l.length hl).1,hnear.trans (hb N rho hr u l.length hl).2⟩

end
end IsingBulk.Tail
