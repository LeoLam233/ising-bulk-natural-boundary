import IsingBulk.Tail.CircularConvolution
import IsingBulk.Tail.SimpleKernelBounds
import IsingBulk.First.ContourIntegrability

/-! Literal original y-Schur kernel majorization and its weighted two-angle
integral. This supplies the convolution step used in ultra-high matchings. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped Topology

def originalYKernel (r t : ℝ) : ℝ := 2/phaseDenominator (r^2) t

theorem anglePoint_mul (r theta phi : ℝ) :
    anglePoint r theta*anglePoint r phi = anglePoint (r^2) (theta+phi) := by
  simp only [anglePoint,circleMap,zero_add,Complex.ofReal_pow,Complex.ofReal_add,
    add_mul,Complex.exp_add]
  ring

theorem original_pair_kernel_norm_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (theta phi : ℝ) : ‖pairKernel (anglePoint r theta) (anglePoint r phi)‖ ≤ originalYKernel r (theta+phi) := by
  have hnum : ‖anglePoint r theta-anglePoint r phi‖ ≤ 2 := by
    have h := norm_sub_le (anglePoint r theta) (anglePoint r phi)
    rw [anglePoint_norm hr,anglePoint_norm hr] at h
    linarith
  rw [pairKernel,norm_div,anglePoint_mul]
  have hden : ‖1-anglePoint (r^2) (theta+phi)‖ = phaseDenominator (r^2) (theta+phi) := by
    simp only [anglePoint,circleMap,zero_add,phaseDenominator]
    congr 3
    ring
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

theorem originalYKernel_periodic (r : ℝ) : Function.Periodic (originalYKernel r) (2*Real.pi) :=
  (phaseDenominator_periodic (r^2)).comp (fun x => 2/x)

theorem originalYKernel_nonneg (r t : ℝ) : 0 ≤ originalYKernel r t := by
  unfold originalYKernel phaseDenominator
  positivity

theorem originalYKernel_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (originalYKernel r) := by
  have hr2 : r^2 < 1 := by nlinarith
  have hn (t : ℝ) : phaseDenominator (r^2) t ≠ 0 := by
    have h := radial_deficit_le_phaseDenominator (sq_nonneg r) t
    linarith
  apply continuous_const.div _ hn
  unfold phaseDenominator
  fun_prop

/-- The y pair in this theorem is the actual source Schur ratio; its full
weighted integral is controlled before multiplying different matching pairs. -/
theorem original_weighted_y_pair_integral_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {R : ℝ → ℝ} (hR : Continuous R) (hRpos : ∀ x : ℝ, 0 ≤ R x) :
    (∫ p in Icc (0:ℝ) (2*Real.pi) ×ˢ Icc (0:ℝ) (2*Real.pi),
      R p.1*R p.2*‖pairKernel (anglePoint r p.1) (anglePoint r p.2)‖) ≤
      (∫ x in Icc (0:ℝ) (2*Real.pi), R x^2)*
      (∫ y in Icc (0:ℝ) (2*Real.pi), originalYKernel r y) := by
  let B := Icc (0:ℝ) (2*Real.pi)
  have hpoint : Continuous (fun p : ℝ × ℝ =>
      pairKernel (anglePoint r p.1) (anglePoint r p.2)) := by
    have hx : Continuous (fun p : ℝ × ℝ => anglePoint r p.1) := (continuous_circleMap 0 r).comp continuous_fst
    have hy : Continuous (fun p : ℝ × ℝ => anglePoint r p.2) := (continuous_circleMap 0 r).comp continuous_snd
    apply (hx.sub hy).div (continuous_const.sub (hx.mul hy))
    intro p
    exact one_sub_mul_ne_zero_of_norm_lt_one (by rw [anglePoint_norm hr]; exact hr1)
      (by rw [anglePoint_norm hr]; exact hr1)
  have hleft : Continuous (fun p : ℝ × ℝ =>
      R p.1*R p.2*‖pairKernel (anglePoint r p.1) (anglePoint r p.2)‖) :=
    ((hR.comp continuous_fst).mul (hR.comp continuous_snd)).mul hpoint.norm
  have hright : Continuous (fun p : ℝ × ℝ => R p.1*R p.2*originalYKernel r (p.1+p.2)) :=
    ((hR.comp continuous_fst).mul (hR.comp continuous_snd)).mul
      ((originalYKernel_continuous hr hr1).comp (continuous_fst.add continuous_snd))
  calc
    _ ≤ ∫ p in B ×ˢ B, R p.1*R p.2*originalYKernel r (p.1+p.2) := by
      apply setIntegral_mono_on
        (hleft.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
        (hright.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
        (measurableSet_Icc.prod measurableSet_Icc)
      intro p hp
      exact mul_le_mul_of_nonneg_left (original_pair_kernel_norm_le hr hr1.le p.1 p.2)
        (mul_nonneg (hRpos p.1) (hRpos p.2))
    _ ≤ _ := weighted_periodic_pair_integral_le (by positivity) hR
      (originalYKernel_continuous hr hr1) (originalYKernel_periodic r) (originalYKernel_nonneg r)

end
end IsingBulk.Tail
