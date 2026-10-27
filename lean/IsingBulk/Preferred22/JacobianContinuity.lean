import IsingBulk.Preferred22.JacobianResolvent

/-! Joint real continuity of the physical Jacobian/resolvent on the complete
balanced contour. This supplies genuine Tonelli measurability independently
of any regularity or majorant for the transported density. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory

theorem preferred_deformed_source_smooth {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (v : Fin N) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => deformedAngles τ B.p B.m θ v) := by
  have hp := B.smooth
  have hm := B.m_smooth
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  unfold deformedAngles balancedShift occupancy
  fun_prop

theorem preferred_source_phase_smooth {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => preferredTotalPhase d ε τ B.p B.m θ) := by
  have hsin : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hterm (v : Fin N) : ContDiff ℝ ∞ (fun θ : Fin N → ℝ =>
      preferredAngularPhase d ε (deformedAngles τ B.p B.m θ v)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hW := (mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ v)
    have hφ : AnalyticAt ℂ (preferredAngularPhase d ε) (deformedAngles τ B.p B.m θ v) :=
      AnalyticAt.comp (f := fun w : ℂ => preferredRadialTrace d ε-Complex.cos w)
        (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper hW) (by fun_prop)
    exact ContDiffAt.comp (f := fun θ : Fin N → ℝ => deformedAngles τ B.p B.m θ v)
      (g := preferredAngularPhase d ε) θ (hφ.contDiffAt.restrict_scalars ℝ)
      (preferred_deformed_source_smooth d B τ v).contDiffAt
  exact ContDiff.sum (fun v (_ : v ∈ Finset.univ) => hterm v)

theorem preferred_source_slope_continuous {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) (v : Fin N) :
    Continuous (fun θ : Fin N → ℝ => actualBumpSlopeVector d B ε τ θ v) := by
  have he : (fun θ : Fin N → ℝ => actualBumpSlopeVector d B ε τ θ v) =
      (fun θ : Fin N → ℝ => preferredPhaseSlope (preferredRadialTrace d ε)
        (deformedAngles τ B.p B.m θ v)) := by
    funext θ
    rw [actual_bump_angle]
    rfl
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro θ
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  have hW : 0 < (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ v)).im := by
    rw [actual_bump_angle]
    exact preferredBumpW_im_pos d B hε hτ hσ.1 hυ.1 _
  exact ContinuousAt.comp (f := fun θ : Fin N → ℝ => deformedAngles τ B.p B.m θ v)
    (g := preferredPhaseSlope (preferredRadialTrace d ε)) (preferredPhaseSlope_hasDerivAt hW).continuousAt
    (preferred_deformed_source_smooth d B τ v).continuous.continuousAt

theorem preferred_actual_denominator_ne_zero {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) :
    ‖1-preferredActualZ d B ε τ θ‖ ≠ 0 := by
  apply norm_ne_zero_iff.mpr
  rw [preferredActualZ_eq_exp d B hε hτ]
  apply preferred_phase_denominator_ne_zero
  let i : Fin N := ⟨0,hN⟩
  have hs : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW := (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hneg := (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2.2.2
  have hsum := preferred_single_phase_attenuation_le_total d B hε hτ θ i
  change (preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im < 0 at hneg
  linarith

theorem preferred_actual_product_continuous {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) :
    Continuous (fun θ : Fin N → ℝ => preferredActualZ d B ε τ θ) := by
  have hG := (preferred_source_phase_smooth (N := N) d B hε hτ).continuous
  simp_rw [preferredActualZ_eq_exp d B hε hτ]
  fun_prop

theorem preferredJacobianResolvent_continuous {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) :
    Continuous (fun θ : Fin N → ℝ => preferredJacobianResolvent d B ε τ θ) := by
  have hf (v : Fin N) : Continuous (fun θ : Fin N → ℝ => ‖actualBumpSlopeVector d B ε τ θ v+1‖) :=
    ((preferred_source_slope_continuous hN d B hε hτ v).add continuous_const).norm
  have hz := preferred_actual_product_continuous (N := N) d B hε hτ
  unfold preferredJacobianResolvent
  exact (continuous_finsetProd _ (fun v _ => hf v)).div
    ((continuous_const.sub hz).norm) (preferred_actual_denominator_ne_zero hN d B hε hτ)

end
end IsingBulk.Preferred22
