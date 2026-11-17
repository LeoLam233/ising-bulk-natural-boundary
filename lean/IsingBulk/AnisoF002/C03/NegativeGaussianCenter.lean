import IsingBulk.AnisoF002.C03.NegativeGaussianDeterminant
import IsingBulk.AnisoF002.C03.NegativeAngularPolar
import Mathlib.MeasureTheory.Group.Prod

/-!
# Separating the center of the actual Gaussian Vandermonde measure

The chart uses the literal first `d` independent constrained coordinates
and the mean coordinate `m`.  Its Jacobian is `d + 1`.  This factor is
proved by two volume-preserving shears and a one-dimensional scaling;
in particular the eventual `1 / sqrt n` in the constrained integral is
retained rather than absorbed into a surface-measure convention.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def gaussianCenterShift (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ (ℝ × (Fin d → ℝ)) where
  toFun z := (z.1, z.2 + fun _ => z.1)
  invFun z := (z.1, z.2 - fun _ => z.1)
  left_inv z := by ext i <;> simp
  right_inv z := by ext i <;> simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) => (z.1, z.2 + fun _ => z.1))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) => (z.1, z.2 - fun _ => z.1))
    fun_prop

def gaussianCenterShear (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ (ℝ × (Fin d → ℝ)) where
  toFun z := (z.1 - ∑ i, z.2 i, z.2)
  invFun z := (z.1 + ∑ i, z.2 i, z.2)
  left_inv z := by simp
  right_inv z := by simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) => (z.1 - ∑ i, z.2 i, z.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) => (z.1 + ∑ i, z.2 i, z.2))
    fun_prop

def gaussianCenterEquiv (d : ℕ) : (ℝ × (Fin d → ℝ)) ≃ᵐ (Fin (d + 1) → ℝ) :=
  (gaussianCenterShift d).trans
    (((Homeomorph.mulLeft₀ ((d + 1 : ℕ) : ℝ) (by positivity)).toMeasurableEquiv.prodCongr
      (MeasurableEquiv.refl _)).trans
      ((gaussianCenterShear d).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)).symm))

theorem gaussianCenterEquiv_apply (d : ℕ) (m : ℝ) (q : Fin d → ℝ) :
    gaussianCenterEquiv d (m, q) =
      fun i => (independentChart d q : Ambient d) i + m := by
  funext i
  change @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
    (((d + 1 : ℕ) : ℝ) * m - ∑ j, (q j + m)) (fun j => q j + m) i = _
  rw [Fin.insertNth_last']
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, independentChart_last, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    ring
  · simp

theorem gaussianCenterShift_measurePreserving (d : ℕ) (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (gaussianCenterShift d) (μ.prod volume) (μ.prod volume) := by
  apply (MeasurePreserving.id μ).skew_product (g := fun m q => q + fun _ : Fin d => m)
  · fun_prop
  · exact Filter.Eventually.of_forall (fun m => map_add_right_eq_self volume (fun _ => m))

theorem gaussianCenterShear_measurePreserving (d : ℕ) :
    MeasurePreserving (gaussianCenterShear d) := by
  have ht : MeasurePreserving (fun z : (Fin d → ℝ) × ℝ =>
      (z.1, z.2 - ∑ i, z.1 i)) := by
    apply (MeasurePreserving.id (volume : Measure (Fin d → ℝ))).skew_product
      (g := fun q m => m - ∑ i, q i)
    · fun_prop
    · exact Filter.Eventually.of_forall (fun q =>
        by simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-∑ i, q i))
  exact Measure.measurePreserving_swap.comp (ht.comp Measure.measurePreserving_swap)

/-- The full coordinate Jacobian, with the original independent measure. -/
theorem gaussianCenterEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (gaussianCenterEquiv d)
      (ENNReal.ofReal ((d + 1 : ℕ) : ℝ) • volume) volume := by
  let n : ℝ := ((d + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  let μ : Measure ℝ := ENNReal.ofReal n • volume
  have hmul : MeasurePreserving (fun m : ℝ => n * m) μ volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [show μ = ENNReal.ofReal n • volume from rfl, Measure.map_smul]
    · simpa only [abs_of_pos hn] using Real.smul_map_volume_mul_left hn.ne'
    · exact (measurable_const_mul n).aemeasurable
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)).symm.comp
    ((gaussianCenterShear_measurePreserving d).comp
      ((hmul.prod (MeasurePreserving.id (volume : Measure (Fin d → ℝ)))).comp
        (gaussianCenterShift_measurePreserving d μ)))
  dsimp only [μ] at h
  rw [Measure.prod_smul_left] at h
  exact h

theorem constrained_shift_norm_sq {d : ℕ} (v : constrainedPlane d) (m : ℝ) :
    (∑ i, ((v : Ambient d) i + m) ^ 2) = ‖v‖ ^ 2 + ((d + 1 : ℕ) : ℝ) * m ^ 2 := by
  rw [constrained_norm_sq]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, constrained_sum, mul_zero,
    zero_mul, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem vandermondeSquared_add {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    RegularTail.vandermondeSquared (fun i => x i + m) =
      RegularTail.vandermondeSquared x := by
  unfold RegularTail.vandermondeSquared
  apply Finset.prod_congr rfl
  intro ij _
  congr 1
  ring

def ordinaryGaussianWeight (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ i, (x i) ^ 2)) * RegularTail.vandermondeSquared x

theorem ordinaryGaussianWeight_center (d : ℕ) (m : ℝ) (q : Fin d → ℝ) :
    ordinaryGaussianWeight (d + 1) (gaussianCenterEquiv d (m, q)) =
      Real.exp (-((d + 1 : ℕ) : ℝ) * m ^ 2) * gaussianWeight (independentChart d q) := by
  rw [ordinaryGaussianWeight, gaussianCenterEquiv_apply, constrained_shift_norm_sq,
    vandermondeSquared_add]
  unfold gaussianWeight planeVandermonde
  rw [neg_add, Real.exp_add]
  ring

def constrainedGaussianIntegral (d : ℕ) : ℝ :=
  ∫ v : constrainedPlane d, gaussianWeight v ∂independentMeasure d

theorem constrainedGaussianIntegral_coordinates (d : ℕ) :
    constrainedGaussianIntegral d =
      ∫ q : Fin d → ℝ, gaussianWeight (independentChart d q) := by
  exact ((independentChart_measurePreserving d).integral_comp
    (independentChart d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    gaussianWeight).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exact center-coordinate separation, before simplifying the scalar square roots. -/
theorem gaussian_center_integral_factorization (d : ℕ) :
    (∫ x : Fin (d + 1) → ℝ, ordinaryGaussianWeight (d + 1) x) =
      ((d + 1 : ℕ) : ℝ) * Real.sqrt (Real.pi / ((d + 1 : ℕ) : ℝ)) *
        constrainedGaussianIntegral d := by
  have h := (gaussianCenterEquiv_measurePreserving d).integral_comp'
    (ordinaryGaussianWeight (d + 1))
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  have he : (fun z : ℝ × (Fin d → ℝ) =>
      ordinaryGaussianWeight (d + 1) (gaussianCenterEquiv d z)) =
      (fun z => Real.exp (-((d + 1 : ℕ) : ℝ) * z.1 ^ 2) *
        gaussianWeight (independentChart d z.2)) := by
    funext z
    exact ordinaryGaussianWeight_center d z.1 z.2
  rw [he] at h
  rw [Measure.volume_eq_prod ℝ (Fin d → ℝ)] at h
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun m : ℝ => Real.exp (-((d + 1 : ℕ) : ℝ) * m ^ 2))
    (fun q : Fin d → ℝ => gaussianWeight (independentChart d q)),
    integral_gaussian, ← constrainedGaussianIntegral_coordinates] at h
  simpa only [smul_eq_mul, mul_assoc] using h.symm

end
end IsingBulk.AnisoF002.NegativeHT.Angular
