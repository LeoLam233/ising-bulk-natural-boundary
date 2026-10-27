import IsingBulk.Preferred22.WeightedRightAnalytic
import IsingBulk.Preferred22.WeightedIntegralJets
import IsingBulk.Preferred22.FiniteBoundaryRegularity
import IsingBulk.Preferred22.SelectedFinitePopulation

/-! Actual parameter derivatives of weighted right integrals, and Cauchy
estimates from genuine continued boundary-density germs. Angular weights
remain smooth real-variable functions and are never analytically continued. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem preferredWeightedRightIntegral_parameter_jets (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) {s : ℂ}
    (hS : 0<(temperatureTrace s).im) (j : ℕ) :
    iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0) s =
      ∫ θ in angularBox n,iteratedDeriv j (fun t : ℂ =>
        ψ (preferredLiftedAngles B.delta (constrainedAngles θ))*
          preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut t
            (preferredLiftedAngles B.delta (constrainedAngles θ))) s := by
  let w := fun θ : Fin (n+1) → ℝ => ψ (preferredLiftedAngles B.delta θ)*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut
      (preferredLiftedAngles B.delta θ):ℂ)
  have hw := preferredWeighted_lifted_weight_continuous d B ψ hψ rcut hr
  have he (θ : Fin n → ℝ) :
      (fun t : ℂ => w (constrainedAngles θ)*preferredBareContourDensity τ B.p B.m t (constrainedAngles θ)) =
      (fun t : ℂ => ψ (preferredLiftedAngles B.delta (constrainedAngles θ))*
        preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut t
          (preferredLiftedAngles B.delta (constrainedAngles θ))) := by
    funext t
    rw [←preferredBareContourDensity_lift τ B.delta B.p B.m B.periodic B.m_periodic]
    simp only [w,preferredBareContourDensity,preferredPhysicalSeed]
    ring
  have hi := (preferred_weighted_contour_integral_jets n d B hτ w hw hS j).1
  have hf : (fun t : ℂ => ∫ θ in angularBox n,
      w (constrainedAngles θ)*preferredBareContourDensity τ B.p B.m t (constrainedAngles θ))=
      preferredWeightedRightIntegral n d B ψ τ rcut 0 := by
    funext t
    unfold preferredWeightedRightIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => congrFun (he θ) t
  rw [hf] at hi
  simpa only [he] using hi

theorem preferredBoundaryAngularDensity_deformed_germ {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (θ : Fin N → ℝ) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    (fun t : ℂ => preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m θ)) =ᶠ[𝓝 s]
      (fun t : ℂ => preferredDeformedPhysicalDensity τ B.p B.m t θ) := by
  obtain ⟨δ,hδ,hU⟩ := preferred_trace_upper_neighborhood hS
  filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
  rw [preferredDeformedPhysicalDensity_eq_complex]
  apply preferredBoundaryAngularDensity_eq_physical
  intro i
  have hW := homotopy_complexW_im_pos (hU t ht).2 hτ (by norm_num : (0:ℝ)≤1)
    B.p B.m θ B.lower_bound (fun x => B.lower_bound (-x))
    (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
  rw [complexW_homotopyRoot_eq] at hW
  exact hW

/-- A constant disk for the actual complete boundary density gives a bound
for the literal weighted physical derivative. The physical continuation
identity and differentiation under the full angular integral are proved. -/
theorem preferred_weighted_right_derivative_from_boundary_disk (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ R M J : ℝ} (hε : 0<ε) (hτ : 0≤τ) (hR : 0<R)
    (hM : 0≤M) (hJ : 0≤J)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (j : ℕ)
    (hweight : ∀ θ : Fin (n+1) → ℝ,
      ‖ψ θ*(preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ:ℂ)‖≤1)
    (hjac : ∀ θ : Fin (n+1) → ℝ,‖(preferredContourMatrix τ B.p B.m θ).det‖≤J)
    (hpoint : ∀ θ∈angularBox n,
      let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      ψ w*(preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0 →
      AnalyticOnNhd ℂ (fun t : ℂ => preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w))
        (Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R) ∧
      ∀ t∈Metric.closedBall (IsingBulk.Branch.radialParameter d.alpha ε) R,
        ‖preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w)‖≤M) :
    ‖iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤
        (J/(((n+1).factorial:ℝ)*(2*Real.pi)^n))*((j.factorial:ℝ)*M/R^j)*(2*Real.pi)^n := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  rw [preferredWeightedRightIntegral_parameter_jets n d B hτ ψ hψ rcut hr
    (preferredRadialTrace_im_pos d hε) j,←angularBox_volume_real]
  apply norm_setIntegral_le_of_norm_le_const_ae
    (by rw [angularBox_volume]; exact ENNReal.ofReal_lt_top)
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))] with θ hθ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  let A := ψ w*(preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)
  let K := A*(preferredContourMatrix τ B.p B.m w).det /
    (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)
  have he : (fun t : ℂ => ψ w*preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut t w)=
      (fun t : ℂ => K*preferredDeformedPhysicalDensity τ B.p B.m t w) := by
    funext t
    simp only [preferredPhysicalSeed,K,A,Nat.add_sub_cancel]
    ring
  change ‖iteratedDeriv j (fun t : ℂ => ψ w*preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut t w) s‖≤_
  rw [he,iteratedDeriv_const_mul_field,norm_mul]
  by_cases hA : A=0
  · simp only [K,hA,zero_mul,zero_div,norm_zero]
    positivity
  · obtain ⟨ha,hb⟩ := hpoint θ hθ hA
    have hbound := IsingBulk.First.cauchy_bound_on_subdisk ha hb hR (Subset.rfl) j
    have hgerm := preferredBoundaryAngularDensity_deformed_germ d B hτ w
      (preferredRadialTrace_im_pos d hε)
    rw [←hgerm.iteratedDeriv_eq]
    have hK : ‖K‖≤J/(((n+1).factorial:ℝ)*(2*Real.pi)^n) := by
      dsimp only [K]
      rw [norm_div,norm_mul]
      simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (mul_le_mul (hweight w) (hjac w) (norm_nonneg _) (by norm_num)).trans_eq (one_mul J)
    simpa only [angularBox_volume_real] using
      mul_le_mul hK hbound (norm_nonneg _) (by positivity)

end
end IsingBulk.Preferred22
