import IsingBulk.HT22.Physical.ComplexAnalytic
import IsingBulk.Preferred22.WeightedIntegralAnalytic
import IsingBulk.HT22.Physical.CellPartition
namespace IsingBulk.HT22.Physical
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem signed_weighted_contour_integral_analyticAt (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : Continuous w) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (fun t : ℂ => ∫ θ in angularBox n,
      w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) s := by
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
  have hi := IsingBulk.First.compact_analytic_shape_integral_analyticAt
    (μ := (volume : Measure (Fin n → ℝ))) hK Metric.isOpen_ball
    (@Physical.complexSignedDensity negative (n+1)) psi hpsi chi hchi hF (Metric.mem_ball_self hδ)
  have heq : (fun t : ℂ => ∫ θ in K,chi θ*Physical.complexSignedDensity negative (t,psi θ)) =
      (fun t : ℂ => ∫ θ in angularBox n,
        w (Physical.constrainedAngles negative n θ)*Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)) := by
    funext t
    rw [setIntegral_congr_set hbox]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by
      simp only [chi,Physical.bareContourDensity,psi,Nat.add_sub_cancel]
      ring
  rw [heq] at hi
  exact hi

theorem anchorPopulationIntegral_analyticAt (negative : Bool) (n : ℕ) (a : Fin (n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (η r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ r) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (anchorPopulationIntegral negative n a τ η B.p B.m r) s := by
  exact signed_weighted_contour_integral_analyticAt negative n d B hτ
    (fun θ => (preferredCellWeight (.anchor a) η B.p B.m r θ:ℂ))
    (Complex.continuous_ofReal.comp (preferredCellWeight_contDiff (.anchor a) η B.p B.m r
      hη B.smooth B.m_smooth hr).continuous) hS
theorem rightPopulationIntegral_analyticAt (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (η r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ r) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (rightPopulationIntegral negative n τ η B.p B.m r) s := by
  exact signed_weighted_contour_integral_analyticAt negative n d B hτ
    (fun θ => (preferredCellWeight .right η B.p B.m r θ:ℂ))
    (Complex.continuous_ofReal.comp (preferredCellWeight_contDiff .right η B.p B.m r
      hη B.smooth B.m_smooth hr).continuous) hS

theorem fullPopulationIntegral_analyticAt (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (η : ℝ → ℝ) (hη : Continuous η) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (fullPopulationIntegral negative n τ η B.p B.m) s := by
  apply signed_weighted_contour_integral_analyticAt negative n d B hτ
    (fun θ => (preferredFullPopulationWeight η B.p B.m θ:ℂ)) _ hS
  have hp := B.smooth.continuous
  have hm := B.m_smooth.continuous
  apply Complex.continuous_ofReal.comp
  unfold preferredFullPopulationWeight fullWeight occupancy
  fun_prop

end
end IsingBulk.HT22.Physical
