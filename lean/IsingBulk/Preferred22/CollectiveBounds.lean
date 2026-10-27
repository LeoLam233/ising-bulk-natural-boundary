import IsingBulk.Preferred22.CollectiveAnalytic
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative bounds for the literal collective quotient and denominator.
The eventual source specialization supplies every scalar bound from the
fixed analytic right domain and actual contour geometry. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem norm_dslope_le_on_convex (f : ℂ → ℂ) (D : Set ℂ) (L : ℝ)
    (hD : Convex ℝ D) (hf : ∀ z∈D, DifferentiableAt ℂ f z)
    (hL : ∀ z∈D, ‖deriv f z‖≤L) (q r : ℂ) (hq : q∈D) (hr : r∈D) :
    ‖dslope f r q‖≤L := by
  by_cases hqr : q=r
  · subst q
    simpa only [dslope_same] using hL r hr
  · rw [dslope_of_ne _ hqr,slope_def_field,norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hqr))).mpr
    exact hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hf z hz).hasDerivAt.hasDerivWithinAt) hL hr hq

/-- Cancellation retains one true U difference, including partial
diagonals. The lower bound is proved by the actual curvature. -/
theorem preferredCollectivePairExtension_norm_bound (s q r : ℂ)
    (D : Set ℂ) (L c : ℝ) (hc : 0<c) (hL : 0≤L) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hv : ∀ z∈D, ‖preferredSourceUQ s z‖≤L)
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : q∈D) (hr : r∈D) :
    ‖preferredCollectivePairExtension s q r‖≤
      ‖preferredMovingInverse s q-preferredMovingInverse s r‖*L/c := by
  have hdU (z : ℂ) (hz : z∈D) : DifferentiableAt ℂ (preferredMovingInverse s) z :=
    (AnalyticAt.comp (f:=fun x : ℂ => (s,x))
      (g:=fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (hU z hz)
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hdv (z : ℂ) (hz : z∈D) : DifferentiableAt ℂ (preferredSourceUQ s) z :=
    (AnalyticAt.comp (f:=fun x : ℂ => (s,x))
      (g:=fun x : ℂ × ℂ => preferredSourceUQ x.1 x.2)
      (preferredSourceUQ_analyticAt_of_joint s z (hU z hz))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hnum := norm_dslope_le_on_convex (preferredMovingInverse s) D L hD hdU hv q r hq hr
  have hden := preferredSourceUQ_dslope_re_lower s D c hD hdv hcurv q r hq hr
  have hden' : c≤‖dslope (preferredSourceUQ s) r q‖ :=
    hden.trans (Complex.re_le_norm _)
  have he : preferredCollectivePairExtension s q r =
      (preferredMovingInverse s q-preferredMovingInverse s r)*
        dslope (preferredMovingInverse s) r q / dslope (preferredSourceUQ s) r q := by
    unfold preferredCollectivePairExtension
    rw [←sub_smul_dslope (preferredMovingInverse s) r q]
    simp only [smul_eq_mul]
    ring
  rw [he,norm_div,norm_mul]
  exact div_le_div₀ (mul_nonneg (norm_nonneg _) hL)
    (mul_le_mul_of_nonneg_left hnum (norm_nonneg _)) hc hden'

/-- A true pair-square denominator has a dimension-polynomial stability
bound under uniform perturbation of its pair differences. -/
theorem collectiveDenominator_perturbation {N : ℕ} (u v : Fin N → ℂ)
    (A E : ℝ) (hA : 0≤A) (hE : 0≤E)
    (hu : ∀ i j, ‖u i-u j‖≤A)
    (hd : ∀ i j, ‖(v i-v j)-(u i-u j)‖≤E) :
    ‖collectiveDenominator v-collectiveDenominator u‖≤
      (N:ℝ)^2*(2*A+E)*E/2 := by
  have hp (i j : Fin N) : ‖(v i-v j)^2-(u i-u j)^2‖≤(2*A+E)*E := by
    have hv : ‖v i-v j‖≤A+E := by
      calc
        _ = ‖(u i-u j)+((v i-v j)-(u i-u j))‖ := by congr 1; ring
        _ ≤ ‖u i-u j‖+‖(v i-v j)-(u i-u j)‖ := norm_add_le _ _
        _ ≤ A+E := add_le_add (hu i j) (hd i j)
    rw [sq_sub_sq,norm_mul]
    have hs : ‖(v i-v j)+(u i-u j)‖≤2*A+E :=
      (norm_add_le _ _).trans (by linarith [hu i j])
    exact mul_le_mul hs (hd i j) (norm_nonneg _) (by positivity)
  have he : collectiveDenominator v-collectiveDenominator u=
      (∑ i, ∑ j, ((v i-v j)^2-(u i-u j)^2))/2 := by
    simp only [collectiveDenominator,Finset.sum_sub_distrib]
    ring
  rw [he,norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ i, ∑ j, ‖(v i-v j)^2-(u i-u j)^2‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, (2*A+E)*E :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by simp; ring

/-- The actual collective field bound, before any source specialization.
Every right-hand input is a scalar regular-domain or R-coercivity bound. -/
theorem preferredResidualCollective_norm_bound {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (D : Set ℂ) (L c A r d : ℝ)
    (hL : 0≤L) (hc : 0<c) (hA : 0≤A) (hr : 0<r) (hd : 0<d)
    (hD : Convex ℝ D) (hq : ∀ i, q i∈D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hv : ∀ z∈D, ‖preferredSourceUQ s z‖≤L)
    (hdot : ∀ i, ‖preferredSourceUDot s (q i)‖≤L)
    (hc₀ : ‖deriv preferredMovingBranch s‖≤L)
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hpair : ∀ i j, ‖preferredMovingInverse s (q i)-preferredMovingInverse s (q j)‖≤A*d)
    (hR : r*d^2≤‖collectiveDenominator (fun i => preferredMovingInverse s (q i))‖)
    (i : Fin N) :
    ‖preferredResidualCollective s q i‖≤L+(N:ℝ)^2*L*(1+L)*A*L/(c*r*d) := by
  have hdotSum : ‖∑ i, preferredSourceUDot s (q i)‖≤(N:ℝ)*L :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hdot i))
  have hvSum : ‖∑ i, preferredSourceUQ s (q i)‖≤(N:ℝ)*L :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hv _ (hq i)))
  have hE : ‖collectiveResidual (fun i => preferredSourceUDot s (q i))
      (fun i => preferredSourceUQ s (q i)) (-deriv preferredMovingBranch s)‖≤(N:ℝ)*L*(1+L) := by
    unfold collectiveResidual
    calc
      _ ≤ ‖∑ i, preferredSourceUDot s (q i)‖+
          ‖deriv preferredMovingBranch s‖*‖∑ i, preferredSourceUQ s (q i)‖ := by
        simpa only [norm_neg,norm_mul] using norm_sub_le
          (-(∑ i, preferredSourceUDot s (q i)))
          ((-deriv preferredMovingBranch s)*(∑ i, preferredSourceUQ s (q i)))
      _ ≤ (N:ℝ)*L+L*((N:ℝ)*L) :=
        add_le_add hdotSum (mul_le_mul hc₀ hvSum (norm_nonneg _) hL)
      _ = _ := by ring
  have hp (j : Fin N) : ‖collectivePair (fun i => preferredMovingInverse s (q i))
      (fun i => preferredSourceUQ s (q i)) i j‖≤A*d*L/c := by
    rw [preferred_collectivePair_eq_extension]
    exact (preferredCollectivePairExtension_norm_bound s (q i) (q j) D L c hc hL hD
      hU hv hcurv (hq i) (hq j)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hpair i j) hL) hc.le)
  have hpSum : ‖∑ j, collectivePair (fun i => preferredMovingInverse s (q i))
      (fun i => preferredSourceUQ s (q i)) i j‖≤(N:ℝ)*(A*d*L/c) :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hp j))
  unfold preferredResidualCollective collectiveField
  calc
    _ ≤ L+((N:ℝ)*L*(1+L)/(r*d^2))*((N:ℝ)*(A*d*L/c)) := by
      apply (norm_add_le _ _).trans
      simp only [norm_neg,norm_mul,norm_div]
      exact add_le_add hc₀ (mul_le_mul
        (div_le_div₀ (by positivity) hE (by positivity) hR) hpSum
        (norm_nonneg _) (by positivity))
    _ = _ := by field_simp

end
end IsingBulk.Preferred22
