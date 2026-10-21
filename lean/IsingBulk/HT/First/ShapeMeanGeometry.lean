import IsingBulk.First.ShapeMeasure
import IsingBulk.First.ShapeVandermonde
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-! Unit-mean splitting of the literal LT ShapeSpace. The product carries
its L2 norm for the isometry, and its ordinary product volume for Fubini. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First MeasureTheory
open scoped BigOperators InnerProductSpace

def unitMeanShapeChart {n : ℕ} (u : ℝ) (x : ShapeSpace n) : Fin (n+1) → ℝ :=
  fun i => x.1 i+u/Real.sqrt (n+1)

theorem unitMeanShapeChart_difference {n : ℕ} (u : ℝ) (x : ShapeSpace n)
    (i j : Fin (n+1)) :
    unitMeanShapeChart u x i-unitMeanShapeChart u x j=x.1 i-x.1 j := by
  unfold unitMeanShapeChart
  ring

theorem firstVandermonde_unitMeanShapeChart {n : ℕ} (u : ℝ) (x : ShapeSpace n) :
    firstVandermonde (unitMeanShapeChart u x)=firstVandermonde (fun i => x.1 i) := by
  unfold firstVandermonde
  simp_rw [unitMeanShapeChart_difference]

/-- Pythagoras for the actual zero-sum subtype and the unit mean coordinate. -/
theorem unitMeanShapeChart_square_sum {n : ℕ} (u : ℝ) (x : ShapeSpace n) :
    (∑ i,unitMeanShapeChart u x i^2)=u^2+‖x‖^2 := by
  have hx : ∑ i,x.1 i=0 := x.2
  have hN : 0 < (n+1:ℝ) := by positivity
  have hr : Real.sqrt (n+1:ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have hmean : (n+1:ℝ)*(u/Real.sqrt (n+1))^2=u^2 := by
    rw [div_pow,Real.sq_sqrt hN.le]
    field_simp
  have hnorm : (∑ i,x.1 i^2)=‖x‖^2 :=
    (EuclideanSpace.real_norm_sq_eq x.1).symm
  calc
    _ = (∑ i,x.1 i^2)+2*(u/Real.sqrt (n+1))*(∑ i,x.1 i)+
        (n+1:ℝ)*(u/Real.sqrt (n+1))^2 := by
      unfold unitMeanShapeChart
      simp only [add_sq,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      rw [← Finset.sum_mul,← Finset.mul_sum]
      ring
    _ = _ := by rw [hx,hnorm,hmean]; ring

/-- Linear embedding of the L2 product using the actual intrinsic ShapeSpace. -/
def unitMeanShapeLinearMap (n : ℕ) :
    WithLp 2 (ℝ × ShapeSpace n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun z := WithLp.toLp 2 (unitMeanShapeChart z.fst z.snd)
  map_add' z w := by
    ext i
    change (z.snd.1 i+w.snd.1 i)+(z.fst+w.fst)/Real.sqrt (n+1)=
      (z.snd.1 i+z.fst/Real.sqrt (n+1))+(w.snd.1 i+w.fst/Real.sqrt (n+1))
    ring
  map_smul' a z := by
    ext i
    change a*z.snd.1 i+(a*z.fst)/Real.sqrt (n+1)=
      a*(z.snd.1 i+z.fst/Real.sqrt (n+1))
    ring

theorem unitMeanShapeLinearMap_norm (n : ℕ) (z : WithLp 2 (ℝ × ShapeSpace n)) :
    ‖unitMeanShapeLinearMap n z‖=‖z‖ := by
  have hleft : ‖unitMeanShapeLinearMap n z‖^2=z.fst^2+‖z.snd‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact unitMeanShapeChart_square_sum z.fst z.snd
  have hright := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs,sq_abs] at hright
  nlinarith [norm_nonneg (unitMeanShapeLinearMap n z),norm_nonneg z]

def unitMeanShapeLinearIsometry (n : ℕ) :
    WithLp 2 (ℝ × ShapeSpace n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toLinearMap := unitMeanShapeLinearMap n
  norm_map' := unitMeanShapeLinearMap_norm n

/-- The explicit inverse is normalized coordinate sum plus the genuine
zero-sum centered tuple. This proves surjectivity without changing the subtype. -/
theorem unitMeanShapeLinearIsometry_surjective (n : ℕ) :
    Function.Surjective (unitMeanShapeLinearIsometry n) := by
  intro y
  let x : ShapeSpace n := ⟨WithLp.toLp 2 (shapeCoordinates (fun i => y i)),
    sum_shapeCoordinates (by positivity : ((n+1:ℕ):ℝ) ≠ 0) (fun i => y i)⟩
  refine ⟨WithLp.toLp 2 ((∑ i,y i)/Real.sqrt (n+1),x),?_⟩
  ext i
  change y i-(∑ j,y j)/((n+1:ℕ):ℝ)+
    ((∑ j,y j)/Real.sqrt (n+1))/Real.sqrt (n+1)=y i
  rw [div_div,← pow_two,Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))]
  push_cast
  ring

def unitMeanShapeIsometry (n : ℕ) :
    WithLp 2 (ℝ × ShapeSpace n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  LinearIsometryEquiv.ofSurjective (unitMeanShapeLinearIsometry n)
    (unitMeanShapeLinearIsometry_surjective n)

@[simp] theorem unitMeanShapeIsometry_apply (n : ℕ) (z : WithLp 2 (ℝ × ShapeSpace n)) :
    unitMeanShapeIsometry n z=WithLp.toLp 2 (unitMeanShapeChart z.fst z.snd) := rfl

/-- The actual unit constant vector in the ambient particle space. -/
def unitMeanVector (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) :=
  unitMeanShapeIsometry n (WithLp.toLp 2 ((1:ℝ),(0:ShapeSpace n)))

@[simp] theorem unitMeanVector_apply (n : ℕ) (i : Fin (n+1)) :
    unitMeanVector n i=(Real.sqrt (n+1))⁻¹ := by
  simp [unitMeanVector,unitMeanShapeChart]

theorem unitMeanVector_norm (n : ℕ) : ‖unitMeanVector n‖=1 := by
  rw [unitMeanVector,(unitMeanShapeIsometry n).norm_map]
  rw [WithLp.norm_toLp_fst, norm_one]

theorem unitMeanVector_orthogonal_shape (n : ℕ) (x : ShapeSpace n) :
    ⟪unitMeanVector n,x.1⟫_ℝ=0 := by
  have hx : unitMeanShapeIsometry n (WithLp.toLp 2 ((0:ℝ),x))=x.1 := by
    ext i
    simp [unitMeanShapeChart]
  rw [unitMeanVector,← hx]
  have hi := LinearIsometryEquiv.inner_map_map (𝕜 := ℝ) (unitMeanShapeIsometry n)
    (WithLp.toLp 2 ((1:ℝ),(0:ShapeSpace n))) (WithLp.toLp 2 ((0:ℝ),x))
  exact hi.trans (by simp)

/-- The normalized-mean decomposition, expressed in the ordinary product
coordinates whose measure is product volume. -/
def unitMeanShapeMeasurableEquiv (n : ℕ) :
    (ℝ × ShapeSpace n) ≃ᵐ (Fin (n+1) → ℝ) :=
  ((MeasurableEquiv.toLp 2 (ℝ × ShapeSpace n)).trans
    (unitMeanShapeIsometry n).toMeasurableEquiv).trans
      (MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ)).symm

@[simp] theorem unitMeanShapeMeasurableEquiv_apply (n : ℕ) (z : ℝ × ShapeSpace n) :
    unitMeanShapeMeasurableEquiv n z=unitMeanShapeChart z.1 z.2 := rfl

/-- There is no √(n+1) multiplier for the UNIT mean and intrinsic shape
volume. That factor belongs only to the separate free-coordinate chart. -/
theorem unitMeanShape_measurePreserving (n : ℕ) :
    MeasurePreserving (unitMeanShapeMeasurableEquiv n) volume volume :=
  ((WithLp.volume_preserving_toLp ℝ (ShapeSpace n)).trans
    (unitMeanShapeIsometry n).measurePreserving).trans
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n+1)))

theorem integral_unitMeanShapeChart (n : ℕ)
    (F : (Fin (n+1) → ℝ) → ℝ) (hF : Integrable F) :
    (∫ y,F y)=∫ x : ShapeSpace n,∫ u : ℝ,F (unitMeanShapeChart u x) := by
  have hp := unitMeanShape_measurePreserving n
  have hi := hp.integrable_comp_of_integrable hF
  have hi' : Integrable (fun z : ℝ × ShapeSpace n => F (unitMeanShapeChart z.1 z.2))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  calc
    _ = ∫ z : ℝ × ShapeSpace n,F (unitMeanShapeMeasurableEquiv n z) :=
      (hp.integral_comp (unitMeanShapeMeasurableEquiv n).measurableEmbedding F).symm
    _ = _ := by
      simp only [unitMeanShapeMeasurableEquiv_apply]
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hi'

end
end IsingBulk.HT.First
