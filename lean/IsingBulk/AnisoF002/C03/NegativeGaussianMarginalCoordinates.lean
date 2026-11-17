import IsingBulk.AnisoF002.C03.NegativeGaussianMehta

/-!
# The actual one-coordinate constrained Gaussian chart

For `n = d + 2`, write `v_1 = x` and
`v_(i+1) = u_i - x/(n-1)`, where the `u` coordinates sum to zero.
The chart is proved to preserve the literal independent-coordinate
Lebesgue measures.  The complete Gaussian and Vandermonde factorization
then supplies the actual marginal, without an assumed density formula.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def marginalScale (d : ℕ) : ℝ := ((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)

theorem marginalScale_pos (d : ℕ) : 0 < marginalScale d := by unfold marginalScale; positivity

theorem marginalScale_identity (d : ℕ) :
    marginalScale d = 1 + (((d + 1 : ℕ) : ℝ))⁻¹ := by
  unfold marginalScale
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

def gaussianMarginalShift (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ (ℝ × (Fin d → ℝ)) where
  toFun z := (z.1, z.2 - fun _ => z.1 / ((d + 1 : ℕ) : ℝ))
  invFun z := (z.1, z.2 + fun _ => z.1 / ((d + 1 : ℕ) : ℝ))
  left_inv z := by ext i <;> simp
  right_inv z := by ext i <;> simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) =>
      (z.1, z.2 - fun _ => z.1 / ((d + 1 : ℕ) : ℝ)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Fin d → ℝ) =>
      (z.1, z.2 + fun _ => z.1 / ((d + 1 : ℕ) : ℝ)))
    fun_prop

def gaussianMarginalEquiv (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ constrainedPlane (d + 1) :=
  (gaussianMarginalShift d).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.trans
      (independentChart (d + 1)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv)

theorem gaussianMarginalEquiv_independent (d : ℕ) (x : ℝ) (q : Fin d → ℝ) :
    gaussianMarginalEquiv d (x, q) =
      independentChart (d + 1) (Fin.cons x (fun i => q i - x / ((d + 1 : ℕ) : ℝ))) := by
  change independentChart (d + 1)
    (@Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) 0 x
      (fun i => q i - x / ((d + 1 : ℕ) : ℝ))) = _
  rw [Fin.insertNth_zero]
  simp only [cast_eq]

theorem gaussianMarginalEquiv_apply (d : ℕ) (x : ℝ) (q : Fin d → ℝ) :
    (gaussianMarginalEquiv d (x, q) : Ambient (d + 1)) =
      WithLp.toLp 2 (Fin.cons x
        (fun i => (independentChart d q : Ambient d) i - x / ((d + 1 : ℕ) : ℝ))) := by
  rw [gaussianMarginalEquiv_independent]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [independentChart_last]
    change -(∑ i : Fin (d + 1), Fin.cons x
        (fun j => q j - x / ((d + 1 : ℕ) : ℝ)) i) =
      (independentChart d q : Ambient d) (Fin.last d) - x / ((d + 1 : ℕ) : ℝ)
    rw [independentChart_last, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · rw [independentChart_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simp

theorem gaussianMarginalEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (gaussianMarginalEquiv d) volume (independentMeasure (d + 1)) := by
  have hs : MeasurePreserving (gaussianMarginalShift d) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun x q => q - fun _ : Fin d => x / ((d + 1 : ℕ) : ℝ))
    · fun_prop
    · exact Filter.Eventually.of_forall (fun x => by
        simpa only [sub_eq_add_neg] using map_add_right_eq_self volume
          (-(fun _ : Fin d => x / ((d + 1 : ℕ) : ℝ))))
  exact (independentChart_measurePreserving (d + 1)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.comp hs)

theorem marginal_quadratic_identity {d : ℕ} (u : constrainedPlane d) (x : ℝ) :
    (∑ i : Fin (d + 2), (Fin.cons x
      (fun j => (u : Ambient d) j - x / ((d + 1 : ℕ) : ℝ)) i) ^ 2) =
      marginalScale d * x ^ 2 + ‖u‖ ^ 2 := by
  rw [Fin.sum_univ_succ, constrained_norm_sq]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, constrained_sum, mul_zero, zero_mul,
    sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [marginalScale_identity]
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem vandermondeSquared_cons {m : ℕ} (x : ℝ) (u : Fin m → ℝ) :
    RegularTail.vandermondeSquared (Fin.cons x u) =
      RegularTail.vandermondeSquared u * ∏ i, (x - u i) ^ 2 := by
  classical
  rw [← vandermonde_det_sq, Matrix.det_vandermonde, Fin.prod_univ_succ,
    Fin.prod_Ioi_zero]
  simp only [Fin.prod_Ioi_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_pow, ← Matrix.det_vandermonde, vandermonde_det_sq, ← Finset.prod_pow]
  have hp : (∏ i, (u i - x) ^ 2) = ∏ i, (x - u i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hp, mul_comm]

theorem marginal_vandermonde_identity {d : ℕ} (u : constrainedPlane d) (x : ℝ) :
    RegularTail.vandermondeSquared (Fin.cons x
      (fun i => (u : Ambient d) i - x / ((d + 1 : ℕ) : ℝ))) =
      planeVandermonde u * ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2 := by
  rw [vandermondeSquared_cons]
  have hs : RegularTail.vandermondeSquared
      (fun i => (u : Ambient d) i - x / ((d + 1 : ℕ) : ℝ)) = planeVandermonde u := by
    simpa only [sub_eq_add_neg, planeVandermonde] using
      vandermondeSquared_add (fun i => (u : Ambient d) i) (-(x / ((d + 1 : ℕ) : ℝ)))
  rw [hs]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [marginalScale_identity]
  ring

/-- Full density factorization in the measure-preserving marginal chart. -/
theorem gaussianWeight_marginal (d : ℕ) (x : ℝ) (q : Fin d → ℝ) :
    gaussianWeight (gaussianMarginalEquiv d (x, q)) =
      Real.exp (-marginalScale d * x ^ 2) * gaussianWeight (independentChart d q) *
        ∏ i, (marginalScale d * x - (independentChart d q : Ambient d) i) ^ 2 := by
  rw [gaussianWeight, constrained_norm_sq, planeVandermonde]
  rw [gaussianMarginalEquiv_apply]
  change Real.exp (-(∑ i, (Fin.cons x
      (fun j => (independentChart d q : Ambient d) j - x / ((d + 1 : ℕ) : ℝ)) i) ^ 2)) *
      RegularTail.vandermondeSquared (Fin.cons x
        (fun j => (independentChart d q : Ambient d) j - x / ((d + 1 : ℕ) : ℝ))) = _
  rw [marginal_quadratic_identity, marginal_vandermonde_identity, neg_add, Real.exp_add]
  unfold gaussianWeight
  ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular
