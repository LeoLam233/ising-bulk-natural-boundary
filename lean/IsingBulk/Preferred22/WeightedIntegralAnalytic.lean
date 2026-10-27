import IsingBulk.Preferred22.PopulationObligations
import IsingBulk.Preferred22.PhysicalDensityRegularity
import IsingBulk.First.CompactIntegralHolomorphic

/-! Actual parameter analyticity of every fixed, smooth localized physical
contour integral. The angular weights remain real and parameter-independent;
no holomorphic extension of any bump function is used. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_trace_upper_neighborhood {s : ℂ}
    (hS : 0<(temperatureTrace s).im) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t∈Metric.ball s δ, t≠0 ∧ 0<(temperatureTrace t).im := by
  have hs : s≠0 := by intro he; rw [he] at hS; simp [temperatureTrace] at hS
  have hc : ContinuousAt (fun t : ℂ => (temperatureTrace t).im) s :=
    Complex.continuous_im.continuousAt.comp (f := temperatureTrace)
      ((continuousAt_id.add (continuousAt_id.inv₀ hs)))
  have he : ∀ᶠ t in 𝓝 s, t≠0 ∧ 0<(temperatureTrace t).im :=
    (eventually_ne_nhds hs).and (hc.eventually (eventually_gt_nhds hS))
  exact Metric.eventually_nhds_iff.mp he

/-- The actual full weighted integral is analytic on the physical upper
trace domain. The full coupled Jacobian and the exact normalizer are retained. -/
theorem preferred_weighted_contour_integral_analyticAt (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : Continuous w) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (fun t : ℂ => ∫ θ in angularBox n,
      w (constrainedAngles θ)*preferredBareContourDensity τ B.p B.m t (constrainedAngles θ)) s := by
  obtain ⟨δ,hδ,hU⟩ := preferred_trace_upper_neighborhood hS
  let K : Set (Fin n → ℝ) := pi univ (fun _ => Icc (-Real.pi) Real.pi)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbox : angularBox n=ᵐ[volume] K := Measure.pi_Ioc_ae_eq_pi_Icc
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun θ => deformedAngles τ B.p B.m (constrainedAngles θ)
  have hpsi : Continuous psi := by
    have hp := B.smooth.continuous
    have hm := B.m_smooth.continuous
    have hco := constrainedAngles_continuous n
    unfold psi deformedAngles balancedShift occupancy
    fun_prop
  let chi : (Fin n → ℝ) → ℂ := fun θ =>
    w (constrainedAngles θ)*(preferredContourMatrix τ B.p B.m (constrainedAngles θ)).det /
      (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)
  have hmat : Continuous (fun θ : Fin (n+1) → ℝ => (preferredContourMatrix τ B.p B.m θ).det) := by
    simp_rw [preferredContourMatrix_eq_full]
    exact (fullAngularJacobian_det_contDiff 1 τ B.p B.m B.smooth B.m_smooth).continuous
  have hchi : Continuous chi := ((hw.comp (constrainedAngles_continuous n)).mul
    (hmat.comp (constrainedAngles_continuous n))).div_const _
  have hF : ∀ t∈Metric.ball s δ, ∀ θ∈K,
      AnalyticAt ℂ (@complexAngularDensity (n+1)) (t,psi θ) := by
    intro t ht θ _
    apply preferred_complexAngularDensity_analyticAt (by omega) t _ (hU t ht).1
    intro i
    have hW := homotopy_complexW_im_pos (hU t ht).2 hτ (by norm_num : (0:ℝ)≤1)
      B.p B.m (constrainedAngles θ) B.lower_bound (fun x => B.lower_bound (-x))
      (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
    rw [complexW_homotopyRoot_eq] at hW
    exact Or.inl hW.ne'
  have hi := IsingBulk.First.compact_analytic_shape_integral_analyticAt
    (μ := (volume : Measure (Fin n → ℝ))) hK Metric.isOpen_ball
    (@complexAngularDensity (n+1)) psi hpsi chi hchi hF (Metric.mem_ball_self hδ)
  have heq : (fun t : ℂ => ∫ θ in K,chi θ*complexAngularDensity (t,psi θ))=
      (fun t : ℂ => ∫ θ in angularBox n,
        w (constrainedAngles θ)*preferredBareContourDensity τ B.p B.m t (constrainedAngles θ)) := by
    funext t
    rw [setIntegral_congr_set hbox]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by
      change chi θ*complexAngularDensity (t,deformedAngles τ B.p B.m (constrainedAngles θ))=_
      rw [← preferredDeformedPhysicalDensity_eq_complex]
      simp only [chi,preferredBareContourDensity,Nat.add_sub_cancel]
      ring
  rw [heq] at hi
  exact hi

/-- Literal selected/mixed-population integral. -/
theorem preferredFullPopulationIntegral_analyticAt (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ) (η : ℝ → ℝ)
    (hη : Continuous η) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (preferredFullPopulationIntegral n τ η B.p B.m) s := by
  apply preferred_weighted_contour_integral_analyticAt n d B hτ
    (fun θ => (preferredFullPopulationWeight η B.p B.m θ:ℂ)) _ hS
  have hp := B.smooth.continuous
  have hm := B.m_smooth.continuous
  apply Complex.continuous_ofReal.comp
  unfold preferredFullPopulationWeight fullWeight occupancy
  fun_prop

/-- Literal lower integral, with its true occupancy cutoff. -/
theorem preferredLowerPopulationIntegral_analyticAt (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ) (η : ℝ → ℝ)
    (hη : Continuous η) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (preferredLowerPopulationIntegral n τ η B.p B.m) s := by
  apply preferred_weighted_contour_integral_analyticAt n d B hτ
    (fun θ => (preferredLowerWeight η B.p B.m θ:ℂ)) _ hS
  have hp := B.smooth.continuous
  have hm := B.m_smooth.continuous
  apply Complex.continuous_ofReal.comp
  unfold preferredLowerWeight lowerWeight occupancy
  fun_prop

/-- Every named-anchor seed and the full right seed are analytic after
integration on the actual one-sided lift. Its seam is handled by the proved
exact periodic-lift identity; no branch discontinuity is ignored. -/
theorem preferredTransportedIntegral_zero_analyticAt (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (cell : PreferredTransportCell (n+1))
    {τ : ℝ} (hτ : 0≤τ) (η r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hr : ContDiff ℝ ∞ r) (hrp : Function.Periodic r (2*Real.pi))
    {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (preferredTransportedIntegral cell B.delta τ η B.p B.m r 0) s := by
  have hc : Continuous (fun θ : Fin (n+1) → ℝ =>
      (preferredCellWeight cell η B.p B.m r θ:ℂ)) :=
    Complex.continuous_ofReal.comp
      (preferredCellWeight_contDiff cell η B.p B.m r hη B.smooth B.m_smooth hr).continuous
  have hi := preferred_weighted_contour_integral_analyticAt n d B hτ
    (fun θ => (preferredCellWeight cell η B.p B.m r θ:ℂ)) hc hS
  have heq : (preferredTransportedIntegral cell B.delta τ η B.p B.m r 0)=
      (fun t : ℂ => ∫ θ in angularBox n,
        (preferredCellWeight cell η B.p B.m r (constrainedAngles θ):ℂ)*
          preferredBareContourDensity τ B.p B.m t (constrainedAngles θ)) := by
    funext t
    rw [preferredTransportedIntegral_zero_eq_unlifted n cell τ B.delta η B.p B.m r
      B.periodic B.m_periodic hrp t]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by
      simp only [preferredPhysicalSeed,preferredBareContourDensity]
      ring
  rw [heq]
  exact hi

end
end IsingBulk.Preferred22
