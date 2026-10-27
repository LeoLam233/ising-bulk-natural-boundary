import IsingBulk.Preferred22.JointDividedDifference
import IsingBulk.Preferred22.SourceMarkedTransport
import IsingBulk.Preferred22.RightDomain

/-! The genuine collective pair quotient across every partial diagonal.
A moving divided difference gives an explicit analytic extension, and the
actual convex-domain curvature excludes its denominator. The full-equality
R pole remains explicit, as required by the source transport proof. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Algebraic divided-difference cancellation, including both coincident
arguments and zero numerator/denominator cases under Lean's total division. -/
theorem pair_quotient_eq_dslope (f g : ℂ → ℂ) (q r : ℂ) :
    (f q-f r)^2/(g q-g r) = (q-r)*(dslope f r q)^2/dslope g r q := by
  by_cases hqr : q=r
  · subst q
    simp
  · rw [dslope_of_ne _ hqr,dslope_of_ne _ hqr,slope_def_field,slope_def_field]
    by_cases hgr : g q-g r=0
    · simp [hgr]
    · field_simp [sub_ne_zero.mpr hqr,hgr]

/-- The actual regular extension, with no arbitrary auxiliary kernel. -/
def preferredCollectivePairExtension (s q r : ℂ) : ℂ :=
  (q-r)*(dslope (preferredMovingInverse s) r q)^2 /
    dslope (preferredSourceUQ s) r q

theorem preferredCollectivePairExtension_eq_quotient (s q r : ℂ) :
    preferredCollectivePairExtension s q r =
      (preferredMovingInverse s q-preferredMovingInverse s r)^2 /
        (preferredSourceUQ s q-preferredSourceUQ s r) :=
  (pair_quotient_eq_dslope _ _ q r).symm

theorem preferred_collectivePair_eq_extension {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (i j : Fin N) :
    collectivePair (fun i => preferredMovingInverse s (q i))
      (fun i => preferredSourceUQ s (q i)) i j = preferredCollectivePairExtension s (q i) (q j) :=
  pair_quotient_eq_dslope _ _ _ _

theorem preferredSourceUDot_analyticAt_of_joint (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) (s,q) := by
  apply (preferredParameterUJet_analyticAt 1 (s,q) hU).congr
  filter_upwards [hU.eventually_analyticAt] with z hz
  simpa only [iteratedDeriv_one,preferredSourceUDot] using
    preferredParameterUJet_eq_iteratedDeriv 1 z.1 z.2 hz

/-- Joint analyticity in the parameter and both moving arguments. -/
theorem preferredCollectivePairExtension_analyticAt (s q r : ℂ)
    (hUq : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hUr : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,r))
    (hden : dslope (preferredSourceUQ s) r q≠0) :
    AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => preferredCollectivePairExtension z.1.1 z.2 z.1.2)
      ((s,r),q) := by
  let F : (ℂ × ℂ) × ℂ → ℂ := fun z => preferredMovingInverse z.1.1 z.2
  let G : (ℂ × ℂ) × ℂ → ℂ := fun z => preferredSourceUQ z.1.1 z.2
  have hf : AnalyticAt ℂ F ((s,r),q) :=
    AnalyticAt.comp (f:=fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g:=fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hUq
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hfT : AnalyticAt ℂ F ((s,r),r) :=
    AnalyticAt.comp (f:=fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g:=fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hUr
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hg : AnalyticAt ℂ G ((s,r),q) :=
    AnalyticAt.comp (f:=fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g:=fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
      (preferredSourceUQ_analyticAt_of_joint s q hUq)
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hgT : AnalyticAt ℂ G ((s,r),r) :=
    AnalyticAt.comp (f:=fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2))
      (g:=fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
      (preferredSourceUQ_analyticAt_of_joint s r hUr)
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hfd := analyticAt_moving_dslope (T:=fun z : ℂ × ℂ => z.2) hf hfT analyticAt_snd
  have hgd := analyticAt_moving_dslope (T:=fun z : ℂ × ℂ => z.2) hg hgT analyticAt_snd
  exact ((analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)).mul (hfd.pow 2)).fun_div hgd hden

/-- The denominator exclusion is derived from actual Uqq curvature on one
convex domain, and includes the derivative value on the partial diagonal. -/
theorem preferredSourceUQ_dslope_re_lower (s : ℂ) (D : Set ℂ) (c : ℝ)
    (hD : Convex ℝ D)
    (hU : ∀ z∈D, DifferentiableAt ℂ (preferredSourceUQ s) z)
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (q r : ℂ) (hq : q∈D) (hr : r∈D) :
    c≤(dslope (preferredSourceUQ s) r q).re := by
  by_cases hqr : q=r
  · subst q
    simpa only [dslope_same] using hcurv r hr
  · rw [dslope_of_ne _ hqr,slope_def_field]
    exact preferred_slope_secant_re_lower s D c hD hU hcurv q r hq hr hqr

theorem preferredSourceUQ_dslope_ne_zero (s : ℂ) (D : Set ℂ) (c : ℝ) (hc : 0<c)
    (hD : Convex ℝ D)
    (hU : ∀ z∈D, DifferentiableAt ℂ (preferredSourceUQ s) z)
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (q r : ℂ) (hq : q∈D) (hr : r∈D) :
    dslope (preferredSourceUQ s) r q≠0 := by
  have hh := preferredSourceUQ_dslope_re_lower s D c hD hU hcurv q r hq hr
  intro hz
  rw [hz,Complex.zero_re] at hh
  linarith

theorem preferredCollectivePairExtension_analyticAt_of_curvature
    (s q r : ℂ) (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re) (hq : q∈D) (hr : r∈D) :
    AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => preferredCollectivePairExtension z.1.1 z.2 z.1.2)
      ((s,r),q) := by
  apply preferredCollectivePairExtension_analyticAt s q r (hU q hq) (hU r hr)
  apply preferredSourceUQ_dslope_ne_zero s D c hc hD _ hcurv q r hq hr
  intro z hz
  have ha := preferredSourceUQ_analyticAt_of_joint s z (hU z hz)
  exact (AnalyticAt.comp (f:=fun x : ℂ => (s,x))
    (g:=fun x : ℂ × ℂ => preferredSourceUQ x.1 x.2) ha
    (analyticAt_const.prod analyticAt_id)).differentiableAt

/-- The literal collective residual is jointly analytic across every partial
diagonal. Only its genuine full-equality R pole is excluded here. -/
theorem preferredResidualCollective_analyticAt {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q i))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hds : ∀ i j, dslope (preferredSourceUQ s) (q j) (q i)≠0)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (q i))≠0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => z.2 i) (s,q) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (s,q))
  have hu (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredMovingInverse z.1 (z.2 i)) (s,q) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU i)
      (analyticAt_fst.prod (hcoord i))
  have hv (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredSourceUQ z.1 (z.2 i)) (s,q) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
      (preferredSourceUQ_analyticAt_of_joint s (q i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have hd (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredSourceUDot z.1 (z.2 i)) (s,q) :=
    AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g:=fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2)
      (preferredSourceUDot_analyticAt_of_joint s (q i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have hc : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => -deriv preferredMovingBranch z.1) (s,q) :=
    (AnalyticAt.comp (f:=fun z : ℂ × (Fin N → ℂ) => z.1)
      (g:=deriv preferredMovingBranch) hB.deriv analyticAt_fst).neg
  have hp (i j : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => collectivePair
        (fun i => preferredMovingInverse z.1 (z.2 i))
        (fun i => preferredSourceUQ z.1 (z.2 i)) i j) (s,q) := by
    simp_rw [preferred_collectivePair_eq_extension]
    exact AnalyticAt.comp
      (f:=fun z : ℂ × (Fin N → ℂ) => ((z.1,z.2 j),z.2 i))
      (g:=fun z : (ℂ × ℂ) × ℂ => preferredCollectivePairExtension z.1.1 z.2 z.1.2)
      (preferredCollectivePairExtension_analyticAt s (q i) (q j) (hU i) (hU j) (hds i j))
      ((analyticAt_fst.prod (hcoord j)).prod (hcoord i))
  have hRa : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => collectiveDenominator (fun i => preferredMovingInverse z.1 (z.2 i))) (s,q) := by
    exact (Finset.analyticAt_fun_sum Finset.univ (fun i _ =>
      Finset.analyticAt_fun_sum Finset.univ (fun j _ => ((hu i).sub (hu j)).pow 2))).div_const
  have hE : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => collectiveResidual
        (fun i => preferredSourceUDot z.1 (z.2 i)) (fun i => preferredSourceUQ z.1 (z.2 i))
          (-deriv preferredMovingBranch z.1)) (s,q) :=
    (Finset.analyticAt_fun_sum Finset.univ (fun i _ => hd i)).neg.sub
      (hc.mul (Finset.analyticAt_fun_sum Finset.univ (fun i _ => hv i)))
  apply AnalyticAt.pi
  intro i
  exact hc.add ((hE.fun_div hRa hR).mul (Finset.analyticAt_fun_sum Finset.univ (fun j _ => hp i j)))

/-- Actual convex curvature discharges every partial-diagonal denominator
in the collective field, rather than assuming collision compatibility. -/
theorem preferredResidualCollective_analyticAt_of_curvature {N : ℕ}
    (s : ℂ) (q : Fin N → ℂ) (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re) (hq : ∀ i, q i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (q i))≠0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) := by
  apply preferredResidualCollective_analyticAt s q (fun i => hU _ (hq i)) hB _ hR
  intro i j
  apply preferredSourceUQ_dslope_ne_zero s D c hc hD _ hcurv _ _ (hq i) (hq j)
  intro z hz
  exact (AnalyticAt.comp (f:=fun x : ℂ => (s,x))
    (g:=fun x : ℂ × ℂ => preferredSourceUQ x.1 x.2)
    (preferredSourceUQ_analyticAt_of_joint s z (hU z hz))
    (analyticAt_const.prod analyticAt_id)).differentiableAt

end
end IsingBulk.Preferred22
