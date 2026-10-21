import IsingBulk.First.RegularMeanError
import IsingBulk.First.MeanErrorShapeContinuity

/-! Fixed-cutoff integration of the actual regular-chart source.
Holomorphy, absolute integrability and every parameter interchange are proved
from the physical analytic neighborhood, before varying the radial parameter. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

theorem actual_mean_separated_shape_continuity (a : RegularChartData) (n : ℕ)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ K : Set ℝ, IsCompact K →
        ∀ v : ℝ → ℂ, Continuous v → MapsTo v K (meanSeparatedAnnulus delta) →
        ∀ w : ℝ → ℂ, ContinuousOn w K → ∀ j : ℕ,
          ContinuousOn (fun p : MeanSideParameters n =>
            (deriv^[j] (fun s => ∫ x in K, w x*meanLocalDensity s p.2.1 a.alpha p.2.2 (v x))) p.1)
            (ball (exp ((a.theta:ℂ)*I),0,0) r) := by
  obtain ⟨Da,hDa,hA⟩ := actual_mean_small_annulus_tube a n ha hb
  obtain ⟨Di,hDi,hI⟩ := actual_mean_separated_integrals a n ha hb
  refine ⟨min Da Di,lt_min hDa hDi,?_⟩
  intro delta hd hdD
  obtain ⟨ra,hra,hAnalytic,hBound⟩ := hA delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨ri,hri,hIntegral⟩ := hI delta hd (hdD.trans (min_le_right _ _))
  let r := min ra ri
  let p₀ : MeanSideParameters n := (exp ((a.theta:ℂ)*I),0,0)
  refine ⟨r,lt_min hra hri,?_⟩
  intro K hK v hv hvK w hw j
  obtain ⟨C,hC,hbnd⟩ := hBound j
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hw
  let F := fun p : MeanSideParameters n => fun x : ℝ =>
    w x*meanParameterIter (complexMeanFullDensity a.alpha) j (meanParameterPullback n (p,v x))
  have hmap : Continuous (fun q : MeanSideParameters n × ℝ => meanParameterPullback n (q.1,v q.2)) :=
    (meanParameterPullback_continuous n).comp (continuous_fst.prodMk (hv.comp continuous_snd))
  have hcont : ContinuousOn (fun q : MeanSideParameters n × ℝ => F q.1 q.2) (ball p₀ r ×ˢ K) := by
    intro q hq
    have hp : ‖q.1-p₀‖ ≤ ra :=
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hq.1 : ‖q.1-p₀‖ < r)).trans (min_le_left _ _)
    have han := meanParameterIter_analyticAt (hAnalytic q.1 hp (v q.2) (hvK hq.2)) j
    have hc : ContinuousAt (fun q : MeanSideParameters n × ℝ =>
        meanParameterIter (complexMeanFullDensity a.alpha) j (meanParameterPullback n (q.1,v q.2))) q :=
      han.continuousAt.comp (f := fun q : MeanSideParameters n × ℝ => meanParameterPullback n (q.1,v q.2)) hmap.continuousAt
    exact ((hw q.2 hq.2).comp continuous_snd.continuousWithinAt (fun _ h => h.2)).mul hc.continuousWithinAt
  have hmajor (p : MeanSideParameters n) (hp : p ∈ ball p₀ r) (x : ℝ) (hx : x ∈ K) :
      ‖F p x‖ ≤ max M 0*C := by
    have hpa : ‖p-p₀‖ ≤ ra :=
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hp : ‖p-p₀‖ < r)).trans (min_le_left _ _)
    exact (norm_mul _ _).trans_le (mul_le_mul ((hM x hx).trans (le_max_left _ _))
      (hbnd p hpa (v x) (hvK hx)) (norm_nonneg _) (le_max_right _ _))
  have hc := compact_parameter_integral_continuousOn (μ := volume) hK F hcont (max M 0*C) hmajor
  apply hc.congr
  intro p hp
  have hparts : ‖p.1-exp ((a.theta:ℂ)*I)‖ < ri ∧ ‖(p.2.1,p.2.2)‖ ≤ ri := by
    have hp' : ‖p.1-exp ((a.theta:ℂ)*I)‖ < r ∧ ‖(p.2.1,p.2.2)‖ < r := by
      have hp0 : ‖p-p₀‖ < r := by simpa only [mem_ball,dist_eq_norm] using hp
      change max ‖p.1-exp ((a.theta:ℂ)*I)‖ ‖p.2-0‖ < r at hp0
      rw [sub_zero] at hp0
      exact max_lt_iff.mp hp0
    exact ⟨hp'.1.trans_le (min_le_right _ _),(hp'.2.trans_le (min_le_right _ _)).le⟩
  have he := (hIntegral K hK v hv hvK w hw).2.1 p.2.1 p.2.2 hparts.2 j p.1 hparts.1
  dsimp only
  rw [he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [F,meanParameterPullback]
    rw [meanParameterIter_actual_density]

theorem actual_mean_error_shape_continuity (a : RegularChartData) (n : ℕ)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ eta : ℝ → ℂ, Continuous eta → ∀ j : ℕ,
        ContinuousOn (fun p : MeanSideParameters n =>
          (deriv^[j] (fun s => meanRegularError eta s p.2.1 a.alpha delta p.2.2)) p.1)
          (ball (exp ((a.theta:ℂ)*I),0,0) r) := by
  obtain ⟨Dc,hDc,hC⟩ := actual_mean_separated_shape_continuity a n ha hb
  obtain ⟨Di,hDi,hI⟩ := actual_mean_separated_integrals a n ha hb
  refine ⟨min Dc Di,lt_min hDc hDi,?_⟩
  intro delta hd hdD
  obtain ⟨rc,hrc,hCont⟩ := hC delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨ri,hri,hInt⟩ := hI delta hd (hdD.trans (min_le_right _ _))
  let r := min rc ri
  let p₀ : MeanSideParameters n := (exp ((a.theta:ℂ)*I),0,0)
  refine ⟨r,lt_min hrc hri,?_⟩
  intro eta heta j
  have hBottom := hCont (Icc (-delta) delta) isCompact_Icc (meanBottomCurve delta)
    (by unfold meanBottomCurve; fun_prop) (meanBottomCurve_annulus hd) (fun _ => 1) continuousOn_const j
  have hRight := hCont (Icc (-delta) 0) isCompact_Icc (meanRightCurve delta)
    (by unfold meanRightCurve; fun_prop) (meanRightCurve_annulus hd) (fun _ => 1) continuousOn_const j
  have hLeft := hCont (Icc (-delta) 0) isCompact_Icc (meanLeftCurve delta)
    (by unfold meanLeftCurve; fun_prop) (meanLeftCurve_annulus hd) (fun _ => 1) continuousOn_const j
  have hEdgeL := hCont (Icc (-2*delta) (-delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanLeftEdge_annulus hd) eta heta.continuousOn j
  have hEdgeR := hCont (Icc delta (2*delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanRightEdge_annulus hd) eta heta.continuousOn j
  simp only [one_mul] at hBottom hRight hLeft
  have hsub : ball p₀ r ⊆ ball p₀ rc := ball_subset_ball (min_le_left _ _)
  have hAll := (((hBottom.mono hsub).add ((continuousOn_const (c := I)).mul (hRight.mono hsub))).sub
    ((continuousOn_const (c := I)).mul (hLeft.mono hsub))).add ((hEdgeL.mono hsub).add (hEdgeR.mono hsub))
  apply hAll.congr
  intro p hp
  dsimp only
  have hp0 : ‖p-p₀‖ < r := by simpa only [mem_ball,dist_eq_norm] using hp
  change max ‖p.1-exp ((a.theta:ℂ)*I)‖ ‖p.2-0‖ < r at hp0
  rw [sub_zero] at hp0
  have hs := ((max_lt_iff.mp hp0).1.trans_le (min_le_right _ _) : ‖p.1-exp ((a.theta:ℂ)*I)‖ < ri)
  have ht := (((max_lt_iff.mp hp0).2.trans_le (min_le_right _ _)).le : ‖(p.2.1,p.2.2)‖ ≤ ri)
  have hB := (hInt (Icc (-delta) delta) isCompact_Icc (meanBottomCurve delta)
    (by unfold meanBottomCurve; fun_prop) (meanBottomCurve_annulus hd) (fun _ => 1) continuousOn_const).1 p.2.1 p.2.2 ht p.1 hs
  have hR := (hInt (Icc (-delta) 0) isCompact_Icc (meanRightCurve delta)
    (by unfold meanRightCurve; fun_prop) (meanRightCurve_annulus hd) (fun _ => 1) continuousOn_const).1 p.2.1 p.2.2 ht p.1 hs
  have hL := (hInt (Icc (-delta) 0) isCompact_Icc (meanLeftCurve delta)
    (by unfold meanLeftCurve; fun_prop) (meanLeftCurve_annulus hd) (fun _ => 1) continuousOn_const).1 p.2.1 p.2.2 ht p.1 hs
  have hE := (hInt (Icc (-2*delta) (-delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanLeftEdge_annulus hd) eta heta.continuousOn).1 p.2.1 p.2.2 ht p.1 hs
  have hF := (hInt (Icc delta (2*delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanRightEdge_annulus hd) eta heta.continuousOn).1 p.2.1 p.2.2 ht p.1 hs
  simp only [one_mul] at hB hR hL
  have heq : (fun s => meanRegularError eta s p.2.1 a.alpha delta p.2.2) =
      (fun s => meanBottomIntegral s p.2.1 a.alpha delta p.2.2+
        I*meanRightIntegral s p.2.1 a.alpha delta p.2.2-
        I*meanLeftIntegral s p.2.1 a.alpha delta p.2.2+
        ((∫ x in Icc (-2*delta) (-delta), eta x*meanLocalDensity s p.2.1 a.alpha p.2.2 (x:ℂ))+
          ∫ x in Icc delta (2*delta), eta x*meanLocalDensity s p.2.1 a.alpha p.2.2 (x:ℂ))) := by
    funext s
    rw [meanRegularError,displacedMeanSides_eq_compact _ _ _ _ hd,meanCutoffEdges]
  rw [heq]
  exact mean_five_terms_iteratedDeriv hB hR hL hE hF j

end
end IsingBulk.First.Regular
