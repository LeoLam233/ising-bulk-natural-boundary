import IsingBulk.HT22.Geometry.SignedCriticalLocalization
import IsingBulk.HT22.First.LocalLimit.SignedCriticalCharts

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First LocalLimit
open scoped Topology BigOperators

def criticalShapeCutoff {n : ℕ} (negative : Bool) (α : ℝ)
    (χ : (Fin n → ℝ) → ℝ) (x : ShapeSpace n) : ℝ :=
  χ (fun i => (if negative then -intrinsicShapeCoordinates x i else intrinsicShapeCoordinates x i)-α)

theorem criticalShapeCutoff_continuous {n : ℕ} (negative : Bool) (α : ℝ)
    (χ : (Fin n → ℝ) → ℝ) (hχ : Continuous χ) :
    Continuous (criticalShapeCutoff negative α χ) := by
  unfold criticalShapeCutoff
  apply hχ.comp
  apply continuous_pi
  intro i
  have h := (continuous_apply i).comp (intrinsicShapeCoordinates_continuous n)
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

@[simp] theorem intrinsicShapeCoordinates_coordinate {n : ℕ} (u : Fin n → ℝ) :
    intrinsicShapeCoordinates (shapeCoordinateEquiv n (WithLp.toLp 2 u))=u := by
  funext i
  simp [intrinsicShapeCoordinates]

theorem criticalShapeCutoff_zero {n : ℕ} (negative : Bool) (α : ℝ)
    (χ : (Fin n → ℝ) → ℝ) :
    criticalShapeCutoff negative α χ 0=χ (fun _ => -α) := by
  cases negative <;> simp [criticalShapeCutoff,intrinsicShapeCoordinates]

theorem criticalShapeCutoff_bound {n : ℕ} (negative : Bool) (α : ℝ)
    (χ : (Fin n → ℝ) → ℝ) (hχ : ∀ u,0≤χ u ∧ χ u≤1) :
    ∀ x,|criticalShapeCutoff negative α χ x|≤1 := by
  intro x
  unfold criticalShapeCutoff
  obtain ⟨hlo,hhi⟩ := hχ (fun i => (if negative then -intrinsicShapeCoordinates x i else intrinsicShapeCoordinates x i)-α)
  exact abs_le.mpr ⟨by linarith,hhi⟩

theorem critical_free_integral_positive {n : ℕ} (α : ℝ) (χ : (Fin n → ℝ) → ℝ) (t : ℂ) :
    (∫u : Fin n → ℝ,(χ (fun i => u i-α):ℂ)*
      (Physical.signedAngularDensity false t (Physical.constrainedAngles false n (fun i => u i-α))/
        (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)))=
    angularLocalIntegral α (fun x => (criticalShapeCutoff false α χ x:ℂ)) t := by
  unfold angularLocalIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    simp only [criticalShapeCutoff,Bool.false_eq_true,ite_false,intrinsicShapeCoordinates_coordinate]
    ring

theorem critical_free_integral_negative {n : ℕ} (α : ℝ) (χ : (Fin n → ℝ) → ℝ) (t : ℂ) :
    (∫u : Fin n → ℝ,(χ (fun i => u i-α):ℂ)*
      (Physical.signedAngularDensity true t (Physical.constrainedAngles true n (fun i => u i-α))/
        (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)))=
    negativeCriticalLocalIntegral α (criticalShapeCutoff true α χ) t := by
  unfold negativeCriticalLocalIntegral
  rw [←integral_neg_eq_self]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    simp only [criticalShapeCutoff,ite_true,intrinsicShapeCoordinates_coordinate,Pi.neg_apply]
    ring

/-- The free-coordinate support radius is chosen before the partition,
and genuinely forces the intrinsic support radius required by FIRST. -/
theorem criticalShapeCutoff_support_radius (n : ℕ) (negative : Bool) (α : ℝ)
    {R : ℝ} (hR : 0<R) : ∃ ρ : ℝ,0<ρ ∧
    ∀ χ : (Fin n → ℝ) → ℝ,
      (∀ u,χ u≠0 → ‖u-(fun _ => -α)‖<ρ) →
      ∀ x,criticalShapeCutoff negative α χ x≠0 → ‖x‖<R := by
  have hc : Continuous (fun u : Fin n → ℝ =>
      shapeCoordinateEquiv n (WithLp.toLp 2 u)) :=
    (shapeCoordinateEquiv n).toContinuousLinearEquiv.continuous.comp (PiLp.continuous_toLp 2 _)
  have h0 : (fun u : Fin n → ℝ => ‖shapeCoordinateEquiv n (WithLp.toLp 2 u)‖) 0<R := by
    simpa only [show WithLp.toLp 2 (0 : Fin n → ℝ)=0 from rfl,map_zero,norm_zero] using hR
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    (hc.norm.continuousAt.eventually (Iio_mem_nhds h0))
  refine ⟨ρ,hρ,?_⟩
  intro χ hχ x hx
  let u : Fin n → ℝ := fun i => if negative then -intrinsicShapeCoordinates x i else intrinsicShapeCoordinates x i
  have hu : ‖u‖<ρ := by
    have hh := hχ (fun i => u i-α) hx
    have he : (fun i => u i-α)-(fun _ => -α)=u := by funext i; simp
    rwa [he] at hh
  have hb := hball (show u∈ball 0 ρ by simpa only [mem_ball,dist_zero_right] using hu)
  change ‖shapeCoordinateEquiv n (WithLp.toLp 2 u)‖<R at hb
  have he : shapeCoordinateEquiv n (WithLp.toLp 2 (intrinsicShapeCoordinates x))=x := by
    apply Subtype.ext
    ext i
    simp only [shapeCoordinateEquiv_apply,shapeExtend_intrinsicShapeCoordinates]
  cases negative with
  | false => simpa only [u,Bool.false_eq_true,ite_false,he] using hb
  | true =>
    have hu' : WithLp.toLp 2 u = -(WithLp.toLp 2 (intrinsicShapeCoordinates x)) := rfl
    simpa only [hu',map_neg,he,norm_neg] using hb

end
end IsingBulk.HT22.Geometry
