import IsingBulk.Tail.CompactRightWindowCurvature
import IsingBulk.Tail.SymmetricDiagonalDerivative

/-! Pair-midpoint slope extraction for the actual coupled phase. -/
namespace IsingBulk.Tail
noncomputable section
open Set
open scoped ContDiff BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def pairDirection {N : ℕ} (i j : Fin N) : Fin N → ℝ := Pi.single i 1-Pi.single j 1

theorem pairDirection_norm_le {N : ℕ} (i j : Fin N) : ‖pairDirection i j‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro a
  simp only [pairDirection,Pi.sub_apply,Pi.single_apply,Real.norm_eq_abs]
  split_ifs <;> norm_num

theorem pairDirection_sq_sum {N : ℕ} {i j : Fin N} (hij : i≠j) :
    ∑ a, (pairDirection i j a)^2=2 := by
  have he (a : Fin N) : (pairDirection i j a)^2=(Pi.single i (1:ℝ) : Fin N → ℝ) a+(Pi.single j (1:ℝ) : Fin N → ℝ) a := by
    by_cases hai : a=i
    · subst a; simp [pairDirection,hij]
    · by_cases haj : a=j
      · subst a; simp [pairDirection,Ne.symm hij]
      · simp [pairDirection,hai,haj]
  simp only [he,Finset.sum_add_distrib]
  norm_num

theorem symmetric_pair_curve_deriv_zero {N : ℕ} (F : (Fin N → ℝ) → ℂ)
    (hF : ContDiff ℝ ∞ F)
    (hsym : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (x : Fin N → ℝ) (i j : Fin N) (hij : x i=x j) :
    deriv (fun t : ℝ => (F (x+t • pairDirection i j)).re) 0=0 := by
  have hd : HasDerivAt (fun t : ℝ => x+t • pairDirection i j) (pairDirection i j) 0 := by
    exact affine_angular_ray_hasDerivAt x (pairDirection i j) 0
  have hFd : HasFDerivAt F (fderiv ℝ F x) (x+(0:ℝ) • pairDirection i j) := by
    simpa using (hF.differentiable (by simp) x).hasFDerivAt
  have hcomp := hFd.comp_hasDerivAt (0:ℝ) hd
  have hzero : fderiv ℝ F x (pairDirection i j)=0 := by
    rw [pairDirection,map_sub,symmetric_coordinate_derivatives_equal F hsym x
      (hF.differentiable (by simp) x) i j hij,sub_self]
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hcomp
  simpa only [hzero,map_zero,Function.comp_def,Complex.reCLM_apply] using hre.deriv

/-- No selected-pair pole is assumed here: symmetry supplies the exact zero at
its midpoint, and the actual second derivative supplies the slope margin. -/
theorem symmetric_pair_curve_slope {N : ℕ} (F : (Fin N → ℝ) → ℂ)
    (hF : ContDiff ℝ ∞ F)
    (hsym : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (x : Fin N → ℝ) (i j : Fin N) (hij : x i=x j) {a k : ℝ} (ha : a≤0)
    (hcurv : ∀ t∈Icc a 0,
      deriv (deriv (fun u : ℝ => (F (x+u • pairDirection i j)).re)) t≤-k) :
    k*(-a)≤deriv (fun u : ℝ => (F (x+u • pairDirection i j)).re) a := by
  let g : ℝ → ℝ := fun u => (F (x+u • pairDirection i j)).re
  have hg : ContDiff ℝ ∞ g := by
    exact Complex.reCLM.contDiff.comp (hF.comp (show ContDiff ℝ ∞ (fun u : ℝ => x+u • pairDirection i j) by fun_prop))
  have hgd : ContDiff ℝ ∞ (deriv g) := by apply ContDiff.deriv'; simpa using hg
  have hh := (convex_Icc a 0).image_sub_le_mul_sub_of_deriv_le hgd.continuous.continuousOn
    (hgd.differentiable (by simp)).differentiableOn
    (fun t ht => hcurv t (interior_subset ht)) a ⟨le_rfl,ha⟩ 0 ⟨ha,le_rfl⟩ ha
  have hz : deriv g 0=0 := symmetric_pair_curve_deriv_zero F hF hsym x i j hij
  rw [hz] at hh
  change k*(-a)≤deriv g a
  linarith


/-- Actual source pair slope on the whole intermediate window. The physical
sheet and all homotopy/occupancy derivatives are supplied by the source, not
by a curvature certificate in the hypotheses. -/
theorem actual_compact_right_pair_slope (d : IsingBulk.Branch.LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ k : ℝ, 0<k ∧ ∀ᶠ H : ℝ in Filter.atTop, ∀ (N : ℕ), 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ (τ lam : ℝ) (x : Fin N → ℝ) (i j : Fin N) (a : ℝ), i≠j → x i=x j → a≤0 →
      0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      (∀ t∈Icc a 0, ∀ l, (x+t • pairDirection i j) l∈
        Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      k*(-a)≤deriv (fun u => currentUnwrappedPhase f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (IsingBulk.Branch.radialParameter d.theta (Real.exp (-H))) (x+u • pairDirection i j)) a := by
  obtain ⟨k,hk,hwindow⟩ := actual_compact_right_window_curvature d hcsmall f hf hp1 hδ hδsmall hD hβ
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := IsingBulk.First.radialDampingMargin_linear hsint hcsmall
  refine ⟨k,hk,?_⟩
  filter_upwards [hwindow,Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he)] with H hcurv hepsE
  intro N hN hND τ lam x i j a hij hmid ha hτ hτ1 hlam hlamB hbox
  let eps := Real.exp (-H)
  let r := Real.exp (-d.c₀*eps)
  let s := IsingBulk.Branch.radialParameter d.theta eps
  have heps : 0<eps := Real.exp_pos _
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(IsingBulk.First.sourceS s).im := by
    have hh := IsingBulk.First.radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  have hF := currentComplexPhase_contDiff hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth
    hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  have hsym : ∀ sigma : Equiv.Perm (Fin N), ∀ y,
      currentComplexPhase f r τ lam s (fun l => y (sigma l))=currentComplexPhase f r τ lam s y := by
    intro sigma y
    exact currentComplexPhase_equiv f r τ lam s y sigma
  have hh := symmetric_pair_curve_slope (currentComplexPhase f r τ lam s) hF hsym x i j hmid ha
    (fun t ht => by
      have hb := hcurv N hN hND τ lam x (pairDirection i j) t hτ hτ1 hlam hlamB
        (pairDirection_norm_le i j) (by rw [pairDirection_sq_sum hij]; norm_num) (hbox t ht)
      simpa only [currentUnwrappedPhase_eq_re] using hb)
  simpa only [currentUnwrappedPhase_eq_re] using hh

end
end IsingBulk.Tail
