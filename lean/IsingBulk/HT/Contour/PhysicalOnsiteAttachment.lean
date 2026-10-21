import IsingBulk.HT.Contour.PhysicalLatticeContour
import IsingBulk.HT.Contour.OnsiteDensityEstimate
import IsingBulk.First.AnnulusProduct

/-!
# The physical onsite coefficient is the actual double-contour coefficient

The collision-regular reduced source is holomorphic through the unit circle.
This permits the genuine normalized contour move from radius one to any
admissible interior radius. The existing all-N residue theorem then identifies
the result with the original double contour, without a physical input premise.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final Set Filter
open scoped BigOperators Topology

theorem physical_sourceW_right_on_annulus {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s y : ℂ} (hm : 1+r⁻¹ < (sourceS s).re)
    (hy : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 1) :
    1 < (sourceW s y).re := by
  have hY := (Complex.re_le_norm ((y+y⁻¹)/2)).trans
    (annular_half_trace_norm hr hy hy1)
  have hi := (one_lt_inv₀ hr).mpr hr1
  simp only [sourceW,Complex.sub_re]
  linarith

/-- Reuse the established continued onsite source, dividing only by the
nonzero angular product. The physical right root is fixed locally by Re W>1. -/
theorem physical_onsiteCanceledDensity_analyticAt {N : ℕ} {s : ℂ} (hs : s ≠ 0)
    {y : Fin N → ℂ} (hy : ∀ i,y i ≠ 0)
    (hW : ∀ i,1 < (sourceW s (y i)).re) :
    AnalyticAt ℂ
      (fun v : Fin N → ℂ => onsiteCanceledDensity (fun i => rightRoot s (v i)) v) y := by
  have dy (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => v i) y :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt y
  have dY : AnalyticAt ℂ (fun v : Fin N → ℂ => coordinateProduct v) y :=
    Finset.analyticAt_fun_prod _ (fun i _ => dy i)
  have hY : coordinateProduct y ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)
  have dW (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => sourceW s (v i)) y :=
    analyticAt_const.sub (((dy i).add ((dy i).inv (hy i))).div analyticAt_const (by norm_num))
  have hnear : ∀ᶠ v in 𝓝 y, ∀ i,1 < (sourceW s (v i)).re :=
    Filter.eventually_all.mpr (fun i =>
      continuousAt_const.eventually_lt
        (Complex.continuous_re.continuousAt.comp (dW i).continuousAt) (hW i))
  have ha := onsite_continuedContourDensity_analyticAt (p := (s,y)) hs hy
    (fun i => Or.inl (Or.inr (hW i)))
  have hc : AnalyticAt ℂ (fun v : Fin N → ℂ => onsiteContinuedContourDensity N (s,v)) y :=
    ha.comp (f := fun v : Fin N → ℂ => (s,v)) (analyticAt_const.prod analyticAt_id)
  apply (hc.div dY hY).congr
  filter_upwards [hnear,dY.continuousAt.eventually_ne hY] with v hv hv0
  have he (i : Fin N) : selectedContinuedRoot s (v i) = rightRoot s (v i) := by
    simp only [selectedContinuedRoot,continuedRoot,ite_eq_left (hv i),rightRoot]
  change coordinateProduct v * onsiteCanceledDensity (fun i => selectedContinuedRoot s (v i)) v /
    coordinateProduct v = _
  simp_rw [he]
  exact mul_div_cancel_left₀ _ hv0

/-- The unit circle is crossed by the canceled source, not by the uncanceled
pair product with its removable reciprocal-pair denominators. -/
theorem physical_onsite_unit_contour_eq_radius (N : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hs : s ≠ 0)
    (hm : 1+r⁻¹ < (sourceS s).re) :
    multiCircleIntegral 1 N
        (fun y => onsiteCanceledDensity (fun i => rightRoot s (y i)) y) =
      multiCircleIntegral r N
        (fun y => onsiteCanceledDensity (fun i => rightRoot s (y i)) y) := by
  apply multiCircleIntegral_radius_eq N hr hr1.le
  intro y hy
  apply (physical_onsiteCanceledDensity_analyticAt hs
    (fun i => norm_pos_iff.mp (hr.trans_le (hy i).1))
    (fun i => physical_sourceW_right_on_annulus hr hr1 hm (hy i).1 (hy i).2)).differentiableAt

/-- Exact onsite attachment for every dimension, with all constants and the
same sufficiently large interior radius required by residue admissibility. -/
theorem physicalLatticeCoefficient_onsite_eq_formFactor (N : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalLatticeCoefficient N t 0 0 = onsiteFormFactor N r (t:ℂ) := by
  have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one ht).ne'
  rw [physicalLatticeCoefficient_eq_unit_contour N ht 0 0]
  simp only [pow_zero,zpow_zero,mul_one]
  rw [physical_onsite_unit_contour_eq_radius N hr hr1 ht0 hm,
    onsite_residue_reduction N r hr (t:ℂ) (rightRoot (t:ℂ))
      (fun y hy => (rightRoot_admissible hr hr1 hm).toTuple N y hy)]
  unfold reducedOnsiteFormFactor
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  have hW (i : Fin N) : 1 < (sourceW (t:ℂ) (y i)).re :=
    sourceW_right_of_margin hr hr1 hm (hy i)
  have he : (fun i => selectedContinuedRoot (t:ℂ) (y i)) =
      (fun i => rightRoot (t:ℂ) (y i)) := by
    funext i
    simp only [selectedContinuedRoot,continuedRoot,ite_eq_left (hW i),rightRoot]
  rw [← he]
  exact onsite_canceledReducedDensity_continued_eq (t:ℂ) y
    (fun i => norm_ne_zero_iff.mp ((hy i).trans_ne hr.ne'))
    (fun i => Or.inl (Or.inr (hW i)))
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one
      ((hy i).trans_lt hr1) ((hy j).trans_lt hr1))

end
end IsingBulk.HT.Contour
