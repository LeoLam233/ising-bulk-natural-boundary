import IsingBulk.First.ShapeGeometry

/-! The Euclidean-to-coordinate volume factor for the actual zero-sum embedding. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Module Set

/-- The source Jacobian in its intrinsic-volume form. -/
theorem volume_shapeCoordinateEquiv_image (n : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume (shapeCoordinateEquiv n '' s) =
      ENNReal.ofReal (Real.sqrt (n+1)) * volume s := by
  have h := (shapeCoordinateEquiv n).toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  rw [(shapeCoordinateEquiv n).finrank_eq,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  change volume (shapeCoordinateEquiv n '' s) =
    ENNReal.ofReal (shapeCoordinateEquiv n).toLinearMap.normDet * volume s at h
  rw [shapeCoordinateEquiv_normDet] at h
  exact h

/-- The coordinate equivalence has volume multiplier √N, established from its
Gram determinant rather than assumed as normalization data. -/
theorem shapeCoordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (shapeCoordinateEquiv n)
      (ENNReal.ofReal (Real.sqrt (n+1)) • volume) volume := by
  have hm : Measurable (shapeCoordinateEquiv n) :=
    (shapeCoordinateEquiv n).toContinuousLinearEquiv.continuous.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  have h := volume_shapeCoordinateEquiv_image n (shapeCoordinateEquiv n ⁻¹' s)
  rw [(shapeCoordinateEquiv n).surjective.image_preimage] at h
  exact h.symm

/-- The literal measure conversion used in the constrained shape period. -/
theorem integral_shapeCoordinateEquiv (n : ℕ) (F : ShapeSpace n → ℂ) :
    (∫ t : EuclideanSpace ℝ (Fin n), F (shapeCoordinateEquiv n t)) =
      (Real.sqrt (n+1))⁻¹ • ∫ t : ShapeSpace n, F t := by
  have h := (shapeCoordinateEquiv_measurePreserving n).integral_comp
    (shapeCoordinateEquiv n).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding F
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
  have hn : Real.sqrt (n+1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [← h, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Product-coordinate Lebesgue measure has the same normalization as its
EuclideanSpace realization. -/
theorem integral_shapeExtend (n : ℕ) (F : ShapeSpace n → ℂ) :
    (∫ t : Fin n → ℝ, F (shapeCoordinateEquiv n (WithLp.toLp 2 t))) =
      (Real.sqrt (n+1))⁻¹ • ∫ t : ShapeSpace n, F t := by
  have h := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (fun t => F (shapeCoordinateEquiv n t))
  exact h.trans (integral_shapeCoordinateEquiv n F)

end
end IsingBulk.First
