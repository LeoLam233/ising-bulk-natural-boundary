import IsingBulk.Tail.MixedBranchLength
import IsingBulk.Tail.MixedPhaseSpectatorIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology BigOperators

def mixedSpectatorMajorant (b B eps t : ℝ) : ℝ :=
  1+B/Real.sqrt (|t-(2*Real.pi-b)|+eps)

theorem mixedSpectatorMajorant_continuous (b B : ℝ) {eps : ℝ} (he : 0<eps) :
    Continuous (mixedSpectatorMajorant b B eps) := by
  unfold mixedSpectatorMajorant
  exact continuous_const.add (continuous_const.div
    (((continuous_id.sub continuous_const).abs.add continuous_const).sqrt)
    (fun t => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg _) he)).ne'))

theorem mixedSpectatorMajorant_one_le (b : ℝ) {B eps : ℝ} (hB : 0≤B) (t : ℝ) :
    1≤mixedSpectatorMajorant b B eps t := by
  unfold mixedSpectatorMajorant
  linarith [div_nonneg hB (Real.sqrt_nonneg (|t-(2*Real.pi-b)|+eps))]

theorem shifted_reciprocal_sqrt_integral_0 {B eps P b : ℝ}
    (hB : 0≤B) (he : 0<eps) (hP : 0≤P) (hb0 : 0≤b) (hbP : b≤P) :
    (∫ u in 0..P,B/Real.sqrt (|u-b|+eps))≤4*B*Real.sqrt P := by
  have hc : Continuous (fun u : ℝ => B/Real.sqrt (|u|+eps)) :=
    continuous_const.div (continuous_abs.add continuous_const).sqrt
      (fun u => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg u) he)).ne')
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => B/Real.sqrt (|u|+eps)) b]
  calc
    _ ≤ ∫ u in -P..P,B/Real.sqrt (|u|+eps) :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun _ => div_nonneg hB (Real.sqrt_nonneg _)))
        (hc.intervalIntegrable _ _)
    _ ≤ _ := reciprocal_sqrt_integral eps P B he hP hB

/-- One common weight dominates branch spectators and the unit compact
measure, with a fixed integral cost on the entire angular interval. -/
theorem mixedSpectatorMajorant_integral {b B eps : ℝ}
    (hb : 0≤b) (hb2 : b≤2*Real.pi) (hB : 0≤B) (he : 0<eps) :
    IntegrableOn (mixedSpectatorMajorant b B eps) (Icc 0 (2*Real.pi)) ∧
      (∫ t in Icc 0 (2*Real.pi),mixedSpectatorMajorant b B eps t)≤
        2*Real.pi+4*B*Real.sqrt (2*Real.pi) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hc := mixedSpectatorMajorant_continuous b B he
  have hk : Continuous (fun t : ℝ => B/Real.sqrt (|t-(2*Real.pi-b)|+eps)) := by
    exact continuous_const.div (((continuous_id.sub continuous_const).abs.add continuous_const).sqrt)
      (fun t => (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg _) he)).ne')
  refine ⟨hc.continuousOn.integrableOn_compact isCompact_Icc,?_⟩
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hπ]
  change (∫ t in 0..2*Real.pi,1+B/Real.sqrt (|t-(2*Real.pi-b)|+eps))≤_
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (hk.intervalIntegrable _ _),intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,mul_one]
  have hh := shifted_reciprocal_sqrt_integral_0 (B := B) (eps := eps) (P := 2*Real.pi)
    (b := 2*Real.pi-b) hB he hπ (by linarith) (by linarith)
  linarith

end
end IsingBulk.Tail
