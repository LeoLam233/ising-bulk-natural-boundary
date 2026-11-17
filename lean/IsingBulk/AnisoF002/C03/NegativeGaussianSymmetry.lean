import IsingBulk.AnisoF002.C03.NegativeGaussianMarginalDensity

/-!
# Coordinate symmetry of the actual constrained Gaussian law

Coordinate permutations act by linear isometries on the zero-sum plane.
Haar uniqueness transfers their volume preservation to the literal
independent-coordinate measure.  The full squared Vandermonde is invariant,
so every coordinate has the actual marginal already proved for coordinate zero.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def constrainedPerm {d : ℕ} (σ : Equiv.Perm (Fin (d + 1))) :
    constrainedPlane d ≃ₗᵢ[ℝ] constrainedPlane d where
  toFun v := ⟨WithLp.toLp 2 (fun i => (v : Ambient d) (σ i)), by
    change (∑ i, (v : Ambient d) (σ i)) = 0
    rw [Equiv.sum_comp σ (fun i => (v : Ambient d) i)]
    exact constrained_sum v⟩
  invFun v := ⟨WithLp.toLp 2 (fun i => (v : Ambient d) (σ.symm i)), by
    change (∑ i, (v : Ambient d) (σ.symm i)) = 0
    rw [Equiv.sum_comp σ.symm (fun i => (v : Ambient d) i)]
    exact constrained_sum v⟩
  left_inv v := by apply Subtype.ext; ext i; simp
  right_inv v := by apply Subtype.ext; ext i; simp
  map_add' v w := by apply Subtype.ext; ext i; rfl
  map_smul' r v := by apply Subtype.ext; ext i; rfl
  norm_map' v := by
    have hs : ‖(⟨WithLp.toLp 2 (fun i => (v : Ambient d) (σ i)), by
        change (∑ i, (v : Ambient d) (σ i)) = 0
        rw [Equiv.sum_comp σ (fun i => (v : Ambient d) i)]
        exact constrained_sum v⟩ : constrainedPlane d)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [constrained_norm_sq, constrained_norm_sq]
      exact Equiv.sum_comp σ (fun i => (v : Ambient d) i ^ 2)
    change ‖(WithLp.toLp 2 (fun i => (v : Ambient d) (σ i)) : Ambient d)‖ = ‖(v : Ambient d)‖
    change ‖(WithLp.toLp 2 (fun i => (v : Ambient d) (σ i)) : Ambient d)‖ ^ 2 =
      ‖(v : Ambient d)‖ ^ 2 at hs
    nlinarith [norm_nonneg (v : Ambient d), norm_nonneg
      (WithLp.toLp 2 (fun i => (v : Ambient d) (σ i)) : Ambient d)]

@[simp] theorem constrainedPerm_apply {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (v : constrainedPlane d) (i : Fin (d + 1)) :
    (constrainedPerm σ v : Ambient d) i = (v : Ambient d) (σ i) := rfl

theorem constrainedPerm_independent_measurePreserving {d : ℕ}
    (σ : Equiv.Perm (Fin (d + 1))) :
    MeasurePreserving (constrainedPerm σ) (independentMeasure d) (independentMeasure d) := by
  rw [Measure.isAddLeftInvariant_eq_smul (independentMeasure d)
    (volume : Measure (constrainedPlane d))]
  exact (constrainedPerm σ).measurePreserving.smul_measure _

theorem vandermondeSquared_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    RegularTail.vandermondeSquared (fun i => x (σ i)) = RegularTail.vandermondeSquared x := by
  rw [← vandermonde_det_sq, ← vandermonde_det_sq]
  have hm : Matrix.vandermonde (fun i => x (σ i)) = (Matrix.vandermonde x).submatrix σ id := rfl
  rw [hm, Matrix.det_permute, mul_pow]
  have hs : (((Equiv.Perm.sign σ : ℤ) : ℝ)) ^ 2 = 1 := by
    rw [pow_two]
    exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
  rw [hs, one_mul]

theorem gaussianWeight_perm {d : ℕ} (σ : Equiv.Perm (Fin (d + 1)))
    (v : constrainedPlane d) : gaussianWeight (constrainedPerm σ v) = gaussianWeight v := by
  rw [gaussianWeight, gaussianWeight, (constrainedPerm σ).norm_map]
  congr 1
  exact vandermondeSquared_perm σ (fun i => (v : Ambient d) i)

theorem constrainedPerm_gaussian_measurePreserving {d : ℕ}
    (σ : Equiv.Perm (Fin (d + 1))) :
    MeasurePreserving (constrainedPerm σ) (gaussianMeasure d) (gaussianMeasure d) := by
  let e := (constrainedPerm σ).toMeasurableEquiv
  refine ⟨e.measurable, ?_⟩
  have hw : (fun v => ENNReal.ofReal (gaussianWeight v)) =
      (fun v => ENNReal.ofReal (gaussianWeight (e v))) := by
    funext v
    rw [show gaussianWeight (e v) = gaussianWeight v from gaussianWeight_perm σ v]
  change (gaussianMeasure d).map e = gaussianMeasure d
  have hm : (independentMeasure d).map e = independentMeasure d :=
    (constrainedPerm_independent_measurePreserving σ).map_eq
  rw [gaussianMeasure, hw, measurableEquiv_map_withDensity_comp e _ _
    (continuous_gaussianWeight d).measurable.ennreal_ofReal, hm]
  rw [← hw]

theorem constrainedPerm_gaussianLaw_measurePreserving {d : ℕ}
    (σ : Equiv.Perm (Fin (d + 1))) :
    MeasurePreserving (constrainedPerm σ) (gaussianLaw d) (gaussianLaw d) := by
  exact (constrainedPerm_gaussian_measurePreserving σ).smul_measure _

/-- Every physical coordinate has exactly the same full constrained Gaussian marginal. -/
theorem gaussianLaw_coordinate_density {d : ℕ} (hd : 0 < d) (i : Fin (d + 2)) :
    (gaussianLaw (d + 1)).map (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) i) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianMarginalDensity d x)) := by
  let σ : Equiv.Perm (Fin (d + 2)) := Equiv.swap 0 i
  have hm := (constrainedPerm_gaussianLaw_measurePreserving σ).map_eq
  have he : (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) 0) ∘
      constrainedPerm σ = (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) i) := by
    funext v
    simp [σ]
  have hfirst := gaussianLaw_first_coordinate_density hd
  rw [← hm, Measure.map_map (by fun_prop) (constrainedPerm σ).continuous.measurable, he] at hfirst
  exact hfirst

end
end IsingBulk.AnisoF002.NegativeHT.Angular
