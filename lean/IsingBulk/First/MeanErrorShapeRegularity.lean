import IsingBulk.First.MeanErrorShapeIntegral
import IsingBulk.First.ActualPostMeanLocalRegularity

/-! Actual holomorphy and absolute integrability of the fixed-cutoff regular
mean error throughout one ordinary source neighborhood. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Set Filter Metric
open scoped Topology

theorem actual_mean_error_shape_regularity {n : ℕ} (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          ∀ rho : ℝ, |rho| ≤ R → ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < R →
            AnalyticAt ℂ (intrinsicMeanErrorIntegral a chi eta rho delta) s ∧
            Integrable (fun x : ShapeSpace n => chi x*
              (meanRegularError eta s rho a.alpha delta (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))) := by
  obtain ⟨Dc,hDc,hC⟩ := actual_mean_error_shape_continuity a n ha hb
  obtain ⟨Db,hDb,hB⟩ := actual_mean_regular_error_bounds a n ha hb
  refine ⟨min Dc Db,lt_min hDc hDb,?_⟩
  intro delta hd hdD
  obtain ⟨rc,hrc,hCont⟩ := hC delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨rb,hrb,hBounds⟩ := hB delta hd (hdD.trans (min_le_right _ _))
  let R := min rc rb/2
  have hR : 0 < R := half_pos (lt_min hrc hrb)
  have hRc : R < rc := (half_lt_self (lt_min hrc hrb)).trans_le (min_le_left _ _)
  have hRb : R < rb := (half_lt_self (lt_min hrc hrb)).trans_le (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro eta heta chi hchi hchis
  have hAnalytic := (hBounds eta heta).1
  let s₀ := exp ((a.theta:ℂ)*I)
  let K : Set (ShapeSpace n) := closedBall 0 R
  let H := fun j s rho x => chi x*((deriv^[j]
    (fun z => meanRegularError eta z rho a.alpha delta (intrinsicShapeCoordinates x))) s)/((n+1).factorial:ℂ)
  have ht (rho : ℝ) (hrho : |rho| ≤ R) (x : ShapeSpace n) (hx : x ∈ K) :
      ‖(rho,intrinsicShapeCoordinates x)‖ ≤ R := by
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le hrho ((norm_intrinsicShapeCoordinates_le x).trans
      (by simpa only [K,mem_closedBall,dist_zero_right] using hx))
  have hz (x : ShapeSpace n) (hx : x ∉ K) : chi x = 0 := by
    by_contra hh
    exact hx (by simpa only [K,mem_closedBall,dist_zero_right] using (hchis x hh).le)
  have hset (j : ℕ) (s : ℂ) (rho : ℝ) : (∫ x in K, H j s rho x) = ∫ x, H j s rho x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp only [H,hz x hx,zero_mul,zero_div])
  intro rho hrho s hs
  have hc (i : ℕ) : ContinuousOn (fun q : ℂ × ShapeSpace n => H i q.1 rho q.2) (ball s₀ R ×ˢ K) := by
    have hmap : Continuous (fun q : ℂ × ShapeSpace n => (q.1,rho,intrinsicShapeCoordinates q.2)) :=
      continuous_fst.prodMk (continuous_const.prodMk ((intrinsicShapeCoordinates_continuous n).comp continuous_snd))
    have hmaps : MapsTo (fun q : ℂ × ShapeSpace n => (q.1,rho,intrinsicShapeCoordinates q.2))
        (ball s₀ R ×ˢ K) (ball (s₀,0,0) rc) := by
      intro q hq
      rw [mem_ball,dist_eq_norm]
      exact (meanSideParameter_norm_le q.1 s₀ rho R (intrinsicShapeCoordinates q.2)
        (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hq.1)) (ht rho hrho q.2 hq.2)).trans_lt hRc
    have hh := (hCont eta heta i).comp hmap.continuousOn hmaps
    exact (((hchi.comp continuous_snd).continuousOn).mul hh).div_const _
  have hd' (i : ℕ) (z : ℂ) (hz : z ∈ ball s₀ R) (x : ShapeSpace n) (hx : x ∈ K) :
      HasDerivAt (fun w => H i w rho x) (H (i+1) z rho x) z := by
    have han := hAnalytic rho (intrinsicShapeCoordinates x) ((ht rho hrho x hx).trans hRb.le) z
      ((by simpa only [mem_ball,dist_eq_norm] using hz : ‖z-s₀‖ < R).trans hRb)
    have hh := ((analytic_iterate_deriv_at han i).differentiableAt.hasDerivAt.const_mul (chi x)).div_const ((n+1).factorial:ℂ)
    convert hh using 1; simp only [H,Function.iterate_succ',Function.comp_def]
  have hfun : (fun z => ∫ x in K, H 0 z rho x) = intrinsicMeanErrorIntegral a chi eta rho delta := by
    funext z
    rw [hset]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [H,intrinsicMeanErrorIntegral,Function.iterate_zero_apply]; ring
  have hAna := compact_joint_jet_integral_analyticAt (μ := (volume : Measure (ShapeSpace n)))
    (isCompact_closedBall (0:ShapeSpace n) R) isOpen_ball (fun i z x => H i z rho x) hc hd'
    (by simpa only [mem_ball,dist_eq_norm] using hs : s ∈ ball s₀ R)
  rw [hfun] at hAna
  refine ⟨hAna,?_⟩
  have hi : Integrable (H 0 s rho) := by
    apply integrable_of_continuousOn_compact_zero_compl (isCompact_closedBall (0:ShapeSpace n) R)
    · exact (hc 0).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨by simpa only [mem_ball,dist_eq_norm] using hs,hx⟩)
    · intro x hx
      simp only [H,hz x hx,zero_mul,zero_div]
  convert hi using 1
  funext x
  dsimp only [H,Function.iterate_zero_apply]
  ring

end
end IsingBulk.First
