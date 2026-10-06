import IsingBulk.First.ShapeSphere
import IsingBulk.First.ShapeMeasure
import IsingBulk.First.ShapeRadialLimit

/-! Weighted polar reduction for the actual constrained Vandermonde period. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Metric Module
open scoped Topology

/-- Convert the radial polar-cone density into ordinary Lebesgue measure. -/
theorem integral_shapeRadialDensity (n d : ℕ) (f : ℝ → ℂ) :
    (∫ r : Ioi (0 : ℝ), (r.1 ^ d) • f r.1 ∂Measure.volumeIoiPow (n-1)) =
      ∫ r : ℝ in Ioi 0, (r ^ (n-1+d)) • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun r => Real.toNNReal (r ^ (n-1)) • ((r ^ d) • f r))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_smul, ← pow_add]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Polar reduction with the source numerator's angular dependence retained. -/
theorem integral_shapeVandermonde_polar {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℂ) :
    (∫ x : ShapeSpace n, shapeVandermondeSq x • f ‖x‖) =
      shapeSphereIntegral n •
        ∫ r : ℝ in Ioi 0, (r ^ (n-1+(n+1)*n)) • f r := by
  let : Nontrivial (ShapeSpace n) := ⟨⟨distinctShape n, 0, distinctShape_ne_zero hn⟩⟩
  let F : ShapeSpace n → ℂ := fun x => shapeVandermondeSq x • f ‖x‖
  let G : sphere (0 : ShapeSpace n) 1 × Ioi (0 : ℝ) → ℂ :=
    fun z => F ((homeomorphUnitSphereProd (ShapeSpace n)).symm z).1
  have hp := (volume : Measure (ShapeSpace n)).measurePreserving_homeomorphUnitSphereProd.integral_comp
    (Homeomorph.measurableEmbedding _) G
  have hg (z : sphere (0 : ShapeSpace n) 1 × Ioi (0 : ℝ)) :
      G z = shapeVandermondeSq z.1.1 • ((z.2.1 ^ ((n+1)*n)) • f z.2.1) := by
    have hnorm : ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = z.2.1 := by
      calc
        ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = ‖z.2.1‖ * ‖z.1.1‖ := norm_smul _ _
        _ = z.2.1 := by
          rw [Real.norm_eq_abs, abs_of_pos z.2.2,
            mem_sphere_zero_iff_norm.mp z.1.2, mul_one]
    change shapeVandermondeSq (z.2.1 • z.1.1) • f ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = _
    rw [hnorm, shapeVandermondeSq_homogeneous, mul_smul, smul_comm]
  calc
    (∫ x : ShapeSpace n, shapeVandermondeSq x • f ‖x‖)
        = ∫ x : ({(0 : ShapeSpace n)}ᶜ : Set (ShapeSpace n)), F x.1
            ∂((volume : Measure (ShapeSpace n)).comap Subtype.val) := by
          rw [integral_subtype_comap (measurableSet_singleton _).compl,
            restrict_compl_singleton]
    _ = ∫ z, G z ∂((volume : Measure (ShapeSpace n)).toSphere.prod
          (Measure.volumeIoiPow (n-1))) := by
          simpa only [G, Homeomorph.symm_apply_apply, finrank_shapeSpace] using hp
    _ = shapeSphereIntegral n •
          ∫ r : Ioi (0 : ℝ), (r.1 ^ ((n+1)*n)) • f r.1
            ∂Measure.volumeIoiPow (n-1) := by
          simp_rw [hg]
          simpa only [shapeSphereIntegral, shapeSphereMeasure] using
            (integral_prod_smul
              (μ := (volume : Measure (ShapeSpace n)).toSphere)
              (ν := Measure.volumeIoiPow (n-1))
              (fun ω : sphere (0 : ShapeSpace n) 1 => shapeVandermondeSq ω.1)
              (fun r : Ioi (0 : ℝ) => (r.1 ^ ((n+1)*n)) • f r.1))
    _ = _ := by rw [integral_shapeRadialDensity]

/-- The exact intrinsic shape integral whose coordinate realization is Jβ. -/
def shapePeriodIntrinsic (n k : ℕ) (Q : ℝ) (c : ℂ) : ℂ :=
  ∫ x : ShapeSpace n, (shapeVandermondeSq x : ℂ) /
    ((Q : ℂ) + c * (‖x‖ : ℂ) ^ 2) ^ (k+1)

/-- The actual free-coordinate integral, with the final dependent coordinate
supplied by the proved linear equivalence. -/
def shapePeriod (n k : ℕ) (Q : ℝ) (c : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ,
    let x := shapeCoordinateEquiv n (WithLp.toLp 2 t)
    (shapeVandermondeSq x : ℂ) / ((Q : ℂ) + c * (‖x‖ : ℂ) ^ 2) ^ (k+1)

theorem shapePeriod_eq_intrinsic (n k : ℕ) (Q : ℝ) (c : ℂ) :
    shapePeriod n k Q c = (Real.sqrt (n+1))⁻¹ • shapePeriodIntrinsic n k Q c := by
  simpa only [shapePeriod, shapePeriodIntrinsic] using
    (integral_shapeExtend n (fun x => (shapeVandermondeSq x : ℂ) /
      ((Q : ℂ) + c * (‖x‖ : ℂ) ^ 2) ^ (k+1)))

theorem shapePeriod_eq_radial {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (Q : ℝ) (c : ℂ) :
    shapePeriod n k Q c = shapeAngularConstant n • shapeRadialIntegral k Q c := by
  rw [shapePeriod_eq_intrinsic]
  have h := integral_shapeVandermonde_polar hn
    (fun r => (((Q : ℂ) + c * (r : ℂ) ^ 2) ^ (k+1))⁻¹)
  rw [hdegree] at h
  have hi : shapePeriodIntrinsic n k Q c = shapeSphereIntegral n • shapeRadialIntegral k Q c := by
    simpa only [shapePeriodIntrinsic, shapeRadialIntegral, shapeRadialKernel,
      shapeQuadratic, Complex.real_smul, Complex.ofReal_pow, div_eq_mul_inv] using h
  rw [hi, smul_smul]
  rfl

end
end IsingBulk.First
