import IsingBulk.AnisoF002.C03.PhysicalContourAnalytic
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic
import IsingBulk.First.AngularFubini

/-!
# Actual double-contour measures and finite coefficient holomorphy

Two possibly different radii are retained in the exact angular Jacobian.
The original iterated contour is converted to a compact ordinary integral
using audited generic one-contour and finite Fubini support.  Its physical
density is then integrated using F002's own compact analytic integral proof.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory Filter IsingBulk.First IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors
open scoped BigOperators Topology

theorem literal_angleTuple_continuous {N : ℕ} (r : ℝ) : Continuous (angleTuple (N := N) r) := by
  unfold angleTuple anglePoint
  fun_prop

theorem literal_angleProductJacobian_continuous {N : ℕ} (r : ℝ) :
    Continuous (angleProductJacobian (N := N) r) := by
  unfold angleProductJacobian angleJacobian anglePoint
  fun_prop

theorem literal_anglePoint_norm {r : ℝ} (hr : 0 ≤ r) (q : ℝ) : ‖anglePoint r q‖ = r := by
  simp only [anglePoint, norm_circleMap_zero, abs_of_nonneg hr]

def literalDoubleAngularIntegrand {N : ℕ} (r R : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (q : (Fin N → ℝ) × (Fin N → ℝ)) : ℂ :=
  angleProductJacobian R q.2 * angleProductJacobian r q.1 *
    f (angleTuple r q.1) (angleTuple R q.2)

theorem literal_doubleContour_eq_box {N : ℕ} (r R : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hf : Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple r q.1) (angleTuple R q.2))) :
    multiCircleIntegral R N (fun y => multiCircleIntegral r N (fun x => f x y)) =
      ∫ q in angleBox N ×ˢ angleBox N, literalDoubleAngularIntegrand r R f q := by
  have hJr := literal_angleProductJacobian_continuous (N := N) r
  have hJR := literal_angleProductJacobian_continuous (N := N) R
  have hinner (q : Fin N → ℝ) : multiCircleIntegral r N (fun x => f x (angleTuple R q)) =
      ∫ p in angleBox N, angleProductJacobian r p * f (angleTuple r p) (angleTuple R q) := by
    rw [multiCircleIntegral_eq_angle]
    exact multiAngleIntegral_eq_box N _ (hJr.mul (hf.comp (continuous_id.prodMk continuous_const)))
  have hinnerC : Continuous (fun q : Fin N → ℝ =>
      multiCircleIntegral r N (fun x => f x (angleTuple R q))) := by
    simp_rw [hinner]
    exact continuous_parametric_integral_of_continuous
      ((hJr.comp continuous_snd).mul (hf.comp (continuous_snd.prodMk continuous_fst))) isCompact_Icc
  have hF : Continuous (literalDoubleAngularIntegrand r R f) :=
    ((hJR.comp continuous_snd).mul (hJr.comp continuous_fst)).mul hf
  have hI : IntegrableOn (literalDoubleAngularIntegrand r R f)
      (angleBox N ×ˢ angleBox N) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have houter : Continuous (fun q : Fin N → ℝ => angleProductJacobian R q *
      multiCircleIntegral r N (fun x => f x (angleTuple R q))) := hJR.mul hinnerC
  rw [multiCircleIntegral_eq_angle, multiAngleIntegral_eq_box N _ houter]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, ← Measure.prod_restrict] at hI
  rw [integral_prod_symm _ hI]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q _
  dsimp only
  rw [hinner, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro p _
  dsimp only [literalDoubleAngularIntegrand]
  ring

theorem literal_doubleContour_swap {N : ℕ} (r R : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hf : Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      f (angleTuple r q.1) (angleTuple R q.2))) :
    multiCircleIntegral R N (fun y => multiCircleIntegral r N (fun x => f x y)) =
      multiCircleIntegral r N (fun x => multiCircleIntegral R N (fun y => f x y)) := by
  rw [literal_doubleContour_eq_box r R f hf,
    literal_doubleContour_eq_box R r (fun y x => f x y)
      (hf.comp (continuous_snd.prodMk continuous_fst))]
  have hs := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin N → ℝ)))
    (ν := volume)).setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding
    (literalDoubleAngularIntegrand R r (fun y x => f x y)) (angleBox N ×ˢ angleBox N)
  rw [← Measure.volume_eq_prod] at hs
  have he : Prod.swap ⁻¹' (angleBox N ×ˢ angleBox N) = angleBox N ×ˢ angleBox N := by
    ext q
    exact and_comm
  rw [he] at hs
  rw [← hs]
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro q _
  dsimp only [literalDoubleAngularIntegrand, Prod.swap]
  ring

theorem literal_fullDensity_continuous_angles {N : ℕ} (hN : 0 < N)
    {lam r rx ry : ℝ} {z : ℂ} (h : ContourAnnulus lam z r)
    (hx : r ≤ rx ∧ rx < 1) (hy : r ≤ ry ∧ ry < 1) :
    Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      fullDensity lam z (angleTuple rx q.1) (angleTuple ry q.2)) := by
  have hc : Continuous (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      (z, angleTuple rx q.1, angleTuple ry q.2)) := (continuous_const (y := z)).prodMk
    (((literal_angleTuple_continuous rx).comp continuous_fst).prodMk
      ((literal_angleTuple_continuous ry).comp continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro q
  apply (literal_fullDensity_joint_analyticAt hN h
    (x := angleTuple rx q.1) (y := angleTuple ry q.2) ?_ ?_).continuousAt.comp
    (f := fun q : (Fin N → ℝ) × (Fin N → ℝ) => (z, angleTuple rx q.1, angleTuple ry q.2)) hc.continuousAt
  · intro i
    change r ≤ ‖anglePoint rx (q.1 i)‖ ∧ ‖anglePoint rx (q.1 i)‖ < 1
    rw [literal_anglePoint_norm (h.1.trans_le hx.1).le]
    exact hx
  · intro i
    change r ≤ ‖anglePoint ry (q.2 i)‖ ∧ ‖anglePoint ry (q.2 i)‖ < 1
    rw [literal_anglePoint_norm (h.1.trans_le hy.1).le]
    exact hy

theorem literal_fixedCoefficient_eq_box {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    unscaledFullCoefficientAtRadius N r lam z =
      (N.factorial : ℂ)⁻¹ * ∫ q in angleBox N ×ˢ angleBox N,
        literalDoubleAngularIntegrand r r (fullDensity lam z) q := by
  unfold unscaledFullCoefficientAtRadius
  rw [literal_doubleContour_eq_box r r _
    (literal_fullDensity_continuous_angles hN h ⟨le_rfl, h.2.1⟩ ⟨le_rfl, h.2.1⟩)]

theorem literal_fixedCoefficient_analyticAt {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    AnalyticAt ℂ (unscaledFullCoefficientAtRadius N r lam) z := by
  let K : Set ((Fin N → ℝ) × (Fin N → ℝ)) := angleBox N ×ˢ angleBox N
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let g : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℂ) × (Fin N → ℂ) :=
    fun q => (angleTuple r q.1, angleTuple r q.2)
  let F : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) → ℂ := fun p =>
    (∏ i, p.2.2 i / (2 * (Real.pi : ℂ))) *
      (∏ i, p.2.1 i / (2 * (Real.pi : ℂ))) * fullDensity lam p.1 p.2.1 p.2.2
  have hg : Continuous g := ((literal_angleTuple_continuous r).comp continuous_fst).prodMk
    ((literal_angleTuple_continuous r).comp continuous_snd)
  have hF : ∀ q ∈ K, AnalyticAt ℂ F (z, g q) := by
    intro q _
    have hcoord (i : Fin N) : AnalyticAt ℂ
        (fun p : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => p.2.1 i) (z, g q) :=
      (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp
        (analyticAt_fst.comp analyticAt_snd)
    have hcoord' (i : Fin N) : AnalyticAt ℂ
        (fun p : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => p.2.2 i) (z, g q) :=
      (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp
        (analyticAt_snd.comp analyticAt_snd)
    apply ((Finset.univ.analyticAt_fun_prod (fun i _ => (hcoord' i).div_const)).mul
      (Finset.univ.analyticAt_fun_prod (fun i _ => (hcoord i).div_const))).mul
    apply literal_fullDensity_joint_analyticAt hN h
    · intro i
      change r ≤ ‖anglePoint r (q.1 i)‖ ∧ ‖anglePoint r (q.1 i)‖ < 1
      rw [literal_anglePoint_norm h.1.le]
      exact ⟨le_rfl, h.2.1⟩
    · intro i
      change r ≤ ‖anglePoint r (q.2 i)‖ ∧ ‖anglePoint r (q.2 i)‖ < 1
      rw [literal_anglePoint_norm h.1.le]
      exact ⟨le_rfl, h.2.1⟩
  have ha : AnalyticAt ℂ (fun w => (N.factorial : ℂ)⁻¹ * ∫ q in K, F (w, g q)) z :=
    (analyticAt_const (v := (N.factorial : ℂ)⁻¹)).mul
      (analyticAt_integral_of_joint_analytic (μ := volume.restrict K) hK
        (self_mem_ae_restrict hK.isClosed.measurableSet) hg hF)
  apply ha.congr
  filter_upwards [literal_contourAnnulus_eventually h] with w hw
  exact (literal_fixedCoefficient_eq_box hN hw).symm

end
end IsingBulk.AnisoF002.RegularTail.C03
