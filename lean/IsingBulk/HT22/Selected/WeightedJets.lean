import IsingBulk.HT22.Physical.ContourDensity
import IsingBulk.HT22.Physical.ComplexAnalytic
import IsingBulk.Preferred22.WeightedIntegralAnalytic

/-! Every actual complex derivative of the complete weighted contour integral
is the integral of its literal parameter derivative. This permits pointwise
continued-sheet Cauchy estimates without assuming a continued integral. -/
namespace IsingBulk.HT22.Selected
open IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

theorem signed_weighted_contour_integral_jets (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : Continuous w) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => ∫ θ in angularBox n,
      w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) s =
      ∫ θ in angularBox n,iteratedDeriv j (fun t : ℂ =>
        w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) s ∧
    IntegrableOn (fun θ : Fin n → ℝ => iteratedDeriv j (fun t : ℂ =>
      w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) s)
        (angularBox n) := by
  obtain ⟨δ,hδ,hU⟩ := preferred_trace_upper_neighborhood hS
  let K : Set (Fin n → ℝ) := pi univ (fun _ => Icc (-Real.pi) Real.pi)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbox : angularBox n=ᵐ[volume] K := Measure.pi_Ioc_ae_eq_pi_Icc
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun θ => deformedAngles τ B.p B.m (Physical.constrainedAngles negative n θ)
  have hpsi : Continuous psi := by
    have hp := B.smooth.continuous
    have hm := B.m_smooth.continuous
    have hco := Physical.constrainedAngles_continuous negative n
    unfold psi deformedAngles balancedShift occupancy
    fun_prop
  let chi : (Fin n → ℝ) → ℂ := fun θ =>
    w (Physical.constrainedAngles negative n θ)*(preferredContourMatrix τ B.p B.m (Physical.constrainedAngles negative n θ)).det /
      (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)
  have hmat : Continuous (fun θ : Fin (n+1) → ℝ => (preferredContourMatrix τ B.p B.m θ).det) := by
    simp_rw [preferredContourMatrix_eq_full]
    exact (fullAngularJacobian_det_contDiff 1 τ B.p B.m B.smooth B.m_smooth).continuous
  have hchi : Continuous chi := ((hw.comp (Physical.constrainedAngles_continuous negative n)).mul
    (hmat.comp (Physical.constrainedAngles_continuous negative n))).div_const _
  have hF : ∀ t∈Metric.ball s δ, ∀ θ∈K,
      AnalyticAt ℂ (@Physical.complexSignedDensity negative (n+1)) (t,psi θ) := by
    intro t ht θ _
    apply Physical.complexSignedDensity_analyticAt_of_off_segment negative (by omega) (hU t ht).1
    intro i
    have hW := homotopy_complexW_im_pos (hU t ht).2 hτ (by norm_num : (0:ℝ)≤1)
      B.p B.m (Physical.constrainedAngles negative n θ) B.lower_bound (fun x => B.lower_bound (-x))
      (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
    rw [complexW_homotopyRoot_eq] at hW
    exact Or.inl hW.ne'
  have hi := IsingBulk.First.compact_analytic_shape_integral_iteratedDeriv
    (μ := (volume : Measure (Fin n → ℝ))) hK Metric.isOpen_ball
    (@Physical.complexSignedDensity negative (n+1)) psi hpsi chi hchi hF j s (Metric.mem_ball_self hδ)
  have hfamily (θ : Fin n → ℝ) :
      (fun t : ℂ => w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) =
      (fun t : ℂ => chi θ*Physical.complexSignedDensity negative (t,psi θ)) := by
    funext t
    simp only [chi,Physical.bareContourDensity,Nat.add_sub_cancel]
    ring
  have hjet (θ : Fin n → ℝ) :
      iteratedDeriv j (fun t : ℂ => w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) s =
      chi θ*IsingBulk.First.jointParameterJet (@Physical.complexSignedDensity negative (n+1)) j (s,psi θ) := by
    rw [hfamily,iteratedDeriv_const_mul_field,IsingBulk.First.jointParameterJet_eq,iteratedDeriv_eq_iterate]
  have heq : (fun t : ℂ => ∫ θ in K,chi θ*Physical.complexSignedDensity negative (t,psi θ)) =
      (fun t : ℂ => ∫ θ in angularBox n,
        w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) := by
    funext t
    rw [setIntegral_congr_set hbox]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => (congrFun (hfamily θ) t).symm
  rw [heq] at hi
  constructor
  · simp_rw [hjet]
    rw [setIntegral_congr_set hbox]
    simpa only [iteratedDeriv_eq_iterate,IsingBulk.First.jointParameterJet_eq] using hi
  · simp_rw [hjet]
    have hc : ContinuousOn (fun θ : Fin n → ℝ =>
        chi θ*IsingBulk.First.jointParameterJet (@Physical.complexSignedDensity negative (n+1)) j (s,psi θ)) K := by
      intro θ hθ
      have ha := (IsingBulk.First.jointParameterJet_analyticAt
        (hF s (Metric.mem_ball_self hδ) θ hθ) j).continuousAt
      exact (hchi.continuousAt.mul (ha.comp
        (f := fun x : Fin n → ℝ => (s,psi x))
        (continuous_const.prodMk hpsi).continuousAt)).continuousWithinAt
    unfold IntegrableOn
    rw [Measure.restrict_congr_set hbox]
    exact hc.integrableOn_compact hK

end
end IsingBulk.HT22.Selected
