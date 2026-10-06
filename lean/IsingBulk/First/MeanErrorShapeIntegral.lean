import IsingBulk.First.MeanErrorShapeContinuity
import IsingBulk.First.CompactJetIntegral
import IsingBulk.First.ActualShapeAmplitude

/-! Outer fixed-cutoff shape integration of the actual regular mean error,
including all-order complex-s interchange and genuine uniform bounds. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Set Filter Metric
open scoped Topology

theorem norm_intrinsicShapeCoordinates_le {n : ℕ} (x : ShapeSpace n) :
    ‖intrinsicShapeCoordinates x‖ ≤ ‖x‖ := by
  apply pi_norm_le_iff_of_nonneg (norm_nonneg x) |>.mpr
  intro j
  exact PiLp.norm_apply_le x.1 j.castSucc

def intrinsicMeanErrorIntegral {n : ℕ} (a : OrderedChartData) (chi : ShapeSpace n → ℂ)
    (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ShapeSpace n, chi x*(meanRegularError eta s rho a.alpha delta (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))

theorem actual_mean_error_shape_integral_bounds {n : ℕ} (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          (∀ rho : ℝ, |rho| ≤ R → ∀ j : ℕ, ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < R →
            (deriv^[j] (intrinsicMeanErrorIntegral a chi eta rho delta)) s =
              ∫ x : ShapeSpace n, chi x*((deriv^[j]
                (fun z => meanRegularError eta z rho a.alpha delta (intrinsicShapeCoordinates x))) s)/((n+1).factorial:ℂ)) ∧
          (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, |rho| ≤ R → ∀ s : ℂ,
            ‖s-exp ((a.theta:ℂ)*I)‖ < R →
            ‖(deriv^[j] (intrinsicMeanErrorIntegral a chi eta rho delta)) s‖ ≤ C) := by
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
  intro eta heta chi hchi hchib hchis
  obtain ⟨hAnalytic,hBound⟩ := hBounds eta heta
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
  have hEq (rho : ℝ) (hrho : |rho| ≤ R) (j : ℕ) (s : ℂ) (hs : ‖s-s₀‖ < R) :
      (deriv^[j] (intrinsicMeanErrorIntegral a chi eta rho delta)) s = ∫ x, H j s rho x := by
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
    have hh := compact_joint_jet_integral_iteratedDeriv (μ := (volume : Measure (ShapeSpace n)))
      (isCompact_closedBall (0:ShapeSpace n) R) isOpen_ball (fun i z x => H i z rho x) hc hd' j s
      (by simpa only [mem_ball,dist_eq_norm] using hs)
    have hfun : (fun z => ∫ x in K, H 0 z rho x) = intrinsicMeanErrorIntegral a chi eta rho delta := by
      funext z
      rw [hset]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [H,intrinsicMeanErrorIntegral,Function.iterate_zero_apply]; ring
    rw [hfun,hset] at hh
    exact hh
  refine ⟨hEq,?_⟩
  intro j
  obtain ⟨C,hC,hbnd⟩ := hBound j
  let B := (C/‖((n+1).factorial:ℂ)‖)*volume.real K
  refine ⟨B+1,by dsimp [B]; positivity,?_⟩
  intro rho hrho s hs
  rw [hEq rho hrho j s hs,← hset]
  apply (norm_setIntegral_le_of_norm_le_const (isCompact_closedBall (0:ShapeSpace n) R).measure_lt_top ?_).trans
    (show B ≤ B+1 by linarith)
  intro x hx
  dsimp only [H]
  rw [norm_div,norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖chi x‖*‖(deriv^[j] (fun z => meanRegularError eta z rho a.alpha delta (intrinsicShapeCoordinates x))) s‖ ≤ 1*C :=
      mul_le_mul (hchib x) (hbnd rho (intrinsicShapeCoordinates x) ((ht rho hrho x hx).trans hRb.le) s (hs.trans hRb))
        (norm_nonneg _) (by positivity)
    _ = C := one_mul _

end
end IsingBulk.First
