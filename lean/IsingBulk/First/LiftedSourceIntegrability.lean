import IsingBulk.First.OnsitePeriodicLift

/-! Compactness and actual absolute integrability for the lifted source pieces.
The small-coordinate support condition itself proves compact support. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff

theorem double_small_support_compact (N : ℕ) (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    HasCompactSupport w := by
  have hs : Function.support w ⊆ closedBall c (1/2) := by
    intro u hu
    rw [mem_closedBall,dist_eq_norm,Prod.norm_def,max_le_iff]
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)).mpr
      intro i
      simpa only [Prod.fst_sub,Pi.sub_apply,Real.norm_eq_abs] using (hsmall u hu i).1
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)).mpr
      intro i
      simpa only [Prod.snd_sub,Pi.sub_apply,Real.norm_eq_abs] using (hsmall u hu i).2
  exact (isCompact_closedBall c (1/2)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs isClosed_closedBall)

theorem double_periodicLift_integrability (N : ℕ) (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2)
    (F : DoubleAngularVector N → ℂ) (hF : Continuous F) :
    IntegrableOn (fun u => (doublePeriodicizeBump c w u:ℂ)*F u) (angleBox N ×ˢ angleBox N) ∧
      Integrable (fun u => (w u:ℂ)*F u) := by
  have hp := (Complex.continuous_ofReal.comp (doublePeriodicizeBump_contDiff c w hw hsmall).continuous).mul hF
  have hc : HasCompactSupport (fun u => (w u:ℂ)*F u) :=
    ((double_small_support_compact N c w hsmall).comp_left (by simp : ((0:ℝ):ℂ)=0)).mul_right
  exact ⟨hp.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc),
    ((Complex.continuous_ofReal.comp hw.continuous).mul hF).integrable_of_hasCompactSupport hc⟩

theorem lifted_source_densities_integrable (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (c : DoubleAngularVector N) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    Integrable (localizedDoubleAngleDensity r s w) ∧ Integrable (localizedOnsiteAngleDensity r s w) := by
  have hroot := globalRoot_admissible hr hr1 hm
  have hD := doubleDensity_continuous_angles N hN r s (globalRoot s)
    (fun theta => hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _))
  have hO := (normalizationDensities_continuous_angles N hN r s (globalRoot s) hroot).1
  have hd := (double_periodicLift_integrability N c w hw hsmall
    (doubleAngularDensityOf r (doubleDensity s)) (doubleAngularDensityOf_continuous N r _ hD)).2
  have ho := (double_periodicLift_integrability N c w hw hsmall
    (doubleAngularDensityOf r (onsiteDensity s)) (doubleAngularDensityOf_continuous N r _ hO)).2
  constructor
  · change Integrable (fun u => localizedDoubleAngleDensity r s w u)
    simpa only [localizedDoubleAngleDensity,doubleAngularDensityOf,mul_assoc] using hd
  · change Integrable (fun u => localizedOnsiteAngleDensity r s w u)
    simpa only [localizedOnsiteAngleDensity,doubleAngularDensityOf,mul_assoc] using ho

end
end IsingBulk.First
