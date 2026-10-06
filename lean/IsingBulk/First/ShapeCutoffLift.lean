import IsingBulk.First.ActualLocalMeanAsymptotic

/-! The constructed real free-coordinate cutoff is the same fixed weight
used by the intrinsic shape limit, via the actual inverse chart. -/
namespace IsingBulk.First
noncomputable section
open Complex Set
open scoped Topology

@[simp] theorem shapeCoordinateEquiv_intrinsicShapeCoordinates {n : ℕ} (x : ShapeSpace n) :
    shapeCoordinateEquiv n (WithLp.toLp 2 (intrinsicShapeCoordinates x)) = x := by
  apply Subtype.ext
  ext j
  simp only [shapeCoordinateEquiv_apply,shapeExtend_intrinsicShapeCoordinates]

def liftShapeCutoff {n : ℕ} (chi : (Fin n → ℝ) → ℝ) (x : ShapeSpace n) : ℂ :=
  (chi (intrinsicShapeCoordinates x):ℂ)

theorem liftShapeCutoff_continuous {n : ℕ} {chi : (Fin n → ℝ) → ℝ} (hchi : Continuous chi) :
    Continuous (liftShapeCutoff chi) :=
  Complex.continuous_ofReal.comp (hchi.comp (intrinsicShapeCoordinates_continuous n))

theorem liftShapeCutoff_zero {n : ℕ} {chi : (Fin n → ℝ) → ℝ} (hchi : chi 0=1) :
    liftShapeCutoff chi 0=1 := by
  change (chi 0:ℂ)=1
  rw [hchi,ofReal_one]

theorem liftShapeCutoff_norm_le_one {n : ℕ} {chi : (Fin n → ℝ) → ℝ}
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1) (x : ShapeSpace n) : ‖liftShapeCutoff chi x‖ ≤ 1 := by
  rw [liftShapeCutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hchi _).1]
  exact (hchi _).2

theorem liftShapeCutoff_support {n : ℕ} {chi : (Fin n → ℝ) → ℝ} {R : ℝ}
    (hchi : ∀ t, chi t ≠ 0 → ‖shapeCoordinateEquiv n (WithLp.toLp 2 t)‖ < R)
    (x : ShapeSpace n) (hx : liftShapeCutoff chi x ≠ 0) : ‖x‖ < R := by
  have hne : chi (intrinsicShapeCoordinates x) ≠ 0 := by
    intro hz
    exact hx (by simp only [liftShapeCutoff,hz,ofReal_zero])
  simpa only [shapeCoordinateEquiv_intrinsicShapeCoordinates] using hchi _ hne

@[simp] theorem liftShapeCutoff_apply_chart {n : ℕ} (chi : (Fin n → ℝ) → ℝ) (t : Fin n → ℝ) :
    liftShapeCutoff chi (shapeCoordinateEquiv n (WithLp.toLp 2 t)) = (chi t:ℂ) := by
  simp only [liftShapeCutoff,intrinsicShapeCoordinates_shapeCoordinateEquiv]


def sourceShapeBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) :=
  {t | ‖shapeCoordinateEquiv n (WithLp.toLp 2 t)‖ < R}

theorem sourceShapeBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (sourceShapeBall n R) := by
  have hc : Continuous (fun t : Fin n → ℝ => shapeCoordinateEquiv n (WithLp.toLp 2 t)) :=
    (shapeCoordinateEquiv n).toContinuousLinearEquiv.continuous.comp (PiLp.continuous_toLp 2 _)
  exact isOpen_lt hc.norm continuous_const

theorem sourceShapeBall_mem_nhds_zero (n : ℕ) {R : ℝ} (hR : 0 < R) :
    sourceShapeBall n R ∈ 𝓝 0 := by
  apply (sourceShapeBall_isOpen n R).mem_nhds
  change ‖shapeCoordinateEquiv n 0‖ < R
  simpa only [map_zero,norm_zero] using hR

end
end IsingBulk.First
