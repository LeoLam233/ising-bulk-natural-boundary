import IsingBulk.Tail.AllBranchExteriorNegativeKernel
import IsingBulk.Tail.MixedBranchCone
import IsingBulk.Tail.MixedCoarea
import IsingBulk.Analysis.BranchAttenuation
import IsingBulk.Analysis.BranchMagnitude
import IsingBulk.Tail.SelectorRegularity
import IsingBulk.Tail.SelectorHypotheses

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.First Set
open scoped BigOperators

lemma current_negative_full_Z_kernel (d : LocalBranchData) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ N : ℕ, ∀ eps t u : ℝ,
      0<eps → eps<r → 0≤t → t<r → u≤0 → |u|<r →
      ∀ (phi : Fin N → ℂ) (v : Fin N), (∀ i, (phi i).im≤0) →
      phi v=currentPhase d eps t u →
      ‖deriv (currentPhase d eps t) u‖/‖1-regularZProduct 0 phi‖ ≤ C/(|u|+eps) := by
  obtain ⟨c,ra,hc,hra,ha⟩ := current_negative_attenuation d
  obtain ⟨cl,B,rm,hcl,hB,hrm,hm⟩ := current_derivative_magnitude d
  let r := min ra rm
  have hr : 0<r := lt_min hra hrm
  let a := c*Real.exp (-c*Real.sqrt (3*r))
  have hac : 0<a := mul_pos hc (Real.exp_pos _)
  refine ⟨B/a,r,div_pos hB hac,hr,?_⟩
  intro N eps t u he heR ht htR hu huR phi v hphi hv
  have hL : 0 < |u|+eps+t := by positivity
  have hLr : |u|+eps+t≤3*r := by linarith
  have hat := ha eps t u he (heR.trans_le (min_le_left _ _)) ht
    (htR.trans_le (min_le_left _ _)) hu (huR.trans_le (min_le_left _ _))
  have hmag := (hm eps t u he (heR.trans_le (min_le_right _ _)) ht
    (htR.trans_le (min_le_right _ _)) (huR.trans_le (min_le_right _ _))).2
  have hkernel := allBranchExterior_Z_attenuation phi hphi v
  have hgap : a*Real.sqrt (|u|+eps+t) ≤ ‖1-regularZProduct 0 phi‖ := by
    have hexp : Real.exp (-c*Real.sqrt (3*r)) ≤ Real.exp (-c*Real.sqrt (|u|+eps+t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_le_sqrt hLr]
    have haux := allBranchExterior_one_sub_exp_neg_lower (c*Real.sqrt (|u|+eps+t))
    have hphiexp : Real.exp ((phi v).im) ≤ Real.exp (-c*Real.sqrt (|u|+eps+t)) :=
      Real.exp_le_exp.mpr (by rw [hv]; linarith)
    have hmul := mul_le_mul_of_nonneg_left hexp (mul_nonneg hc.le (Real.sqrt_nonneg (|u|+eps+t)))
    dsimp [a]
    simp only [neg_mul] at hexp hphiexp hmul ⊢
    nlinarith
  have hs : 0 < Real.sqrt (|u|+eps+t) := Real.sqrt_pos.mpr hL
  have hb := div_le_div₀ (div_nonneg hB.le (Real.sqrt_nonneg _)) hmag (mul_pos hac hs) hgap
  have heq : (B/Real.sqrt (|u|+eps+t))/(a*Real.sqrt (|u|+eps+t)) = (B/a)/(|u|+eps+t) := by
    have hh := Real.sq_sqrt hL.le
    field_simp
    rw [hh]
  rw [heq] at hb
  exact hb.trans (div_le_div_of_nonneg_left (div_pos hB hac).le (by positivity) (by linarith))

/-- Actual coupled plateau with all occupancy retained and original lambda=0 included. -/
theorem mixed_actual_negative_Z_kernel (d : LocalBranchData) :
    ∃ C r tau0 : ℝ, 0<C ∧ 0<r ∧ 0<tau0 ∧
      ∀ (N : ℕ) (eps tau lam : ℝ) (f : SelectorFunctions) (theta : Fin N → ℝ) (v : Fin N),
      0<N → 0<eps → eps<r → 0≤tau → tau<tau0 → 0≤lam → lam≤1 →
      RegularSelector f → (∀ x, f.p x≤1) →
      (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps) < (IsingBulk.First.sourceS (radialParameter d.theta eps)).im →
      f.p (theta v)=0 → f.m (theta v)=1 →
      theta v+d.thetaB-2*Real.pi≤0 → |theta v+d.thetaB-2*Real.pi|<r →
      let y := deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta
      let phi := fun i => mixedSourcePhase (radialParameter d.theta eps) (y i)
      ‖mixedSourceSlope (radialParameter d.theta eps) (y v)‖/‖1-regularZProduct 0 phi‖ ≤
        C/(|theta v+d.thetaB-2*Real.pi|+eps) := by
  obtain ⟨C,rk,hC,hrk,hkernel⟩ := current_negative_full_Z_kernel d
  obtain ⟨rb,hrb,hbranch⟩ := current_branch_inclusion d
  let r := min rk rb
  have hr : 0<r := lt_min hrk hrb
  refine ⟨C,r,d.tau*r,hC,hr,mul_pos d.tau_pos hr,?_⟩
  intro N eps tau lam f theta v hN he heR ht htR hl hl1 hf hp1 hmargin hpv hmv hu huR
  dsimp only
  let t := lam*occupancy (fun i => f.p (theta i))/(N:ℝ)
  let u := theta v+d.thetaB-2*Real.pi
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun i => hf.p_nonneg (theta i))
  have hPN := occupancy_le (fun i => hp1 (theta i))
  have ht0 : 0≤t := by dsimp [t]; positivity
  have ht1 : t≤1 := (div_le_one hn).mpr ((mul_le_of_le_one_left hP0 hl1).trans hPN)
  have hs0 : 0≤(tau/d.tau)*t := mul_nonneg (div_nonneg ht d.tau_pos.le) ht0
  have hsR : (tau/d.tau)*t<r := by
    have hh : tau/d.tau<r := (div_lt_iff₀ d.tau_pos).mpr (by simpa [mul_comm] using htR)
    exact (mul_le_of_le_one_right (div_nonneg ht d.tau_pos.le) ht1).trans_lt hh
  have hplateau : deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta v =
      plateauY d.c₀ eps d.tau ((tau/d.tau)*t) d.thetaB u := by
    rw [plateauY_rescale_tau]
    exact deformedPoint_current_plateau f d.thetaB d.c₀ eps tau lam theta v hpv hmv
  have hW : ∀ i, 0 < (sourceW (radialParameter d.theta eps)
      (deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta i)).im := by
    intro i
    have hrad : Real.exp (-d.c₀*eps)<1 := by rw [Real.exp_lt_one_iff]; nlinarith [d.c₀_pos]
    exact (sourceW_upper_of_margin (Real.exp_pos _) hrad hmargin
      (deformedPoint_zero_norm f (Real.exp_pos _).le tau theta i)).trans_le
      (deformed_sourceW_im_ge hN f (Real.exp_pos _) ht hl theta _ hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero i)
  have hb := hbranch eps ((tau/d.tau)*t) u he (heR.trans_le (min_le_right _ _)) hs0
    (hsR.trans_le (min_le_right _ _)) (huR.trans_le (min_le_right _ _))
  rw [hplateau,mixedSourceSlope_current_deriv d eps ((tau/d.tau)*t) u hb.1 hb.2]
  apply hkernel N eps ((tau/d.tau)*t) u he (heR.trans_le (min_le_left _ _)) hs0
    (hsR.trans_le (min_le_left _ _)) hu (huR.trans_le (min_le_left _ _))
  · intro i
    exact (mixedSourcePhase_upper_bounds (hW i)).2.2.le
  · rw [hplateau,mixedSourcePhase_current]

lemma mixed_negative_log_integral {r eps : ℝ} (hr : 0 ≤ r) (he : 0 < eps) :
    (∫ u in -r..0, (|u|+eps)⁻¹) = Real.log (r+eps)-Real.log eps := by
  have hder (u : ℝ) (hu : u ∈ uIcc (-r) 0) :
      HasDerivAt (fun v => -Real.log (eps-v)) ((|u|+eps)⁻¹) u := by
    rw [uIcc_of_le (by linarith)] at hu
    have hp : 0 < eps-u := by linarith [hu.2]
    have hh := ((Real.hasDerivAt_log hp.ne').comp u ((hasDerivAt_id u).const_sub eps)).neg
    simpa [Function.comp_def,Pi.neg_apply,abs_of_nonpos hu.2,sub_eq_add_neg,add_comm] using! hh
  have hc : ContinuousOn (fun u : ℝ => (|u|+eps)⁻¹) (uIcc (-r) 0) :=
    (continuous_abs.continuousOn.add continuousOn_const).inv₀ (fun u _ => (add_pos_of_nonneg_of_pos (abs_nonneg u) he).ne')
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hc.intervalIntegrable)
  simpa [sub_eq_add_neg,add_comm] using hh

lemma mixed_negative_log_majorant {r eps C : ℝ} (hr : 0 ≤ r) (he : 0 < eps)
    (F : ℝ → ℂ) (hF : ContinuousOn F (Icc (-r) 0))
    (hb : ∀ u ∈ Icc (-r) 0, ‖F u‖ ≤ C/(|u|+eps)) :
    IntervalIntegrable F MeasureTheory.volume (-r) 0 ∧
      ‖∫ u in -r..0, F u‖ ≤ C*(Real.log (r+eps)-Real.log eps) := by
  have hr0 : -r ≤ 0 := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => C/(|u|+eps)) MeasureTheory.volume (-r) 0 := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuous_abs.continuousOn.add continuousOn_const)
      (fun u _ => (add_pos_of_nonneg_of_pos (abs_nonneg u) he).ne')
  refine ⟨hF.intervalIntegrable_of_Icc hr0,?_⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le hr0
    (Filter.Eventually.of_forall (fun u hu => hb u (Ioc_subset_Icc_self hu))) hi
  apply hh.trans_eq
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,mixed_negative_log_integral hr he]

end
end IsingBulk.Tail
