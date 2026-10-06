import IsingBulk.First.MeanShapeContinuity

/-! Joint continuity of every actual mean-error jet on one common shape and
parameter neighborhood, before outer fixed-cutoff shape integration. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

theorem mean_five_terms_iteratedDeriv {B R L E F : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hR : AnalyticAt ℂ R s) (hL : AnalyticAt ℂ L s)
    (hE : AnalyticAt ℂ E s) (hF : AnalyticAt ℂ F s) (j : ℕ) :
    (deriv^[j] (fun z => B z+I*R z-I*L z+(E z+F z))) s =
      (deriv^[j] B) s+I*(deriv^[j] R) s-I*(deriv^[j] L) s+
        ((deriv^[j] E) s+(deriv^[j] F) s) := by
  simp only [← iteratedDeriv_eq_iterate]
  have hIR : ContDiffAt ℂ j (fun z => I*R z) s := ((analyticAt_const (v := I)).mul hR).contDiffAt
  have hIL : ContDiffAt ℂ j (fun z => I*L z) s := ((analyticAt_const (v := I)).mul hL).contDiffAt
  have hBR : ContDiffAt ℂ j (fun z => B z+I*R z) s := hB.contDiffAt.add hIR
  have hBRL : ContDiffAt ℂ j (fun z => B z+I*R z-I*L z) s := hBR.sub hIL
  have hEF : ContDiffAt ℂ j (fun z => E z+F z) s := hE.contDiffAt.add hF.contDiffAt
  rw [iteratedDeriv_fun_add hBRL hEF,
    iteratedDeriv_fun_sub hBR hIL,
    iteratedDeriv_fun_add hB.contDiffAt hIR,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add hE.contDiffAt hF.contDiffAt]

theorem actual_mean_error_shape_continuity (a : OrderedChartData) (n : ℕ)
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
end IsingBulk.First
