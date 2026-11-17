import IsingBulk.AnisoF002.C03.RegularCollisionKernel
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Integrable majorant of the complete scaled first-collision integral

The Vandermonde uses all n+1 constrained angles and Lebesgue measure uses
the actual n independent coordinates.  The precise integrability budget
is n + 2*choose(n+1,2) < 2p.  Both first-singularity derivative orders
satisfy this budget, unlike an unweighted model pole estimate.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def collisionRationalMajorant (n p : ℕ) (q : Fin n → ℝ) : ℝ :=
  ‖edgeVandermondeSquared (complexAngles (flatConstrainedAngles q))‖ /
    (1 + angularQuadratic (flatConstrainedAngles q)) ^ p

theorem flatConstrainedAngles_norm_le {n : ℕ} (q : Fin n → ℝ) :
    ‖flatConstrainedAngles q‖ ≤ ((n : ℝ) + 1) * ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [flatConstrainedAngles, Fin.snoc_last, norm_neg]
    calc
      ‖∑ j, q j‖ ≤ ∑ j, ‖q j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, ‖q‖ := Finset.sum_le_sum (fun j _ => norm_le_pi_norm q j)
      _ ≤ ((n : ℝ) + 1) * ‖q‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith [norm_nonneg q]
  · simp only [flatConstrainedAngles, Fin.snoc_castSucc]
    exact (norm_le_pi_norm q j).trans (by nlinarith [norm_nonneg q, Nat.cast_nonneg (α := ℝ) n])

theorem flatConstrainedAngles_quadratic_lower {n : ℕ} (q : Fin n → ℝ) :
    ‖q‖ ^ 2 ≤ angularQuadratic (flatConstrainedAngles q) := by
  apply (norm_square_le_angularQuadratic q).trans
  unfold angularQuadratic
  rw [Fin.sum_univ_castSucc]
  simp only [flatConstrainedAngles, Fin.snoc_castSucc, Fin.snoc_last, neg_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem edgeVandermondeSquared_norm_bound {N : ℕ} (q : Fin N → ℝ) :
    ‖edgeVandermondeSquared (complexAngles q)‖ ≤ (2 * ‖q‖) ^ (2 * N.choose 2) := by
  simp only [edgeVandermondeSquared, norm_prod, norm_pow]
  calc
    (∏ ij ∈ indexPairs N, ‖complexAngles q ij.1 - complexAngles q ij.2‖ ^ 2) ≤
        ∏ _ij ∈ indexPairs N, (2 * ‖q‖) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
      intro ij _
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖complexAngles q ij.1 - complexAngles q ij.2‖ ≤
            ‖complexAngles q ij.1‖ + ‖complexAngles q ij.2‖ := norm_sub_le _ _
        _ ≤ 2 * ‖q‖ := by
          simp only [complexAngles, Complex.norm_real]
          linarith [norm_le_pi_norm q ij.1, norm_le_pi_norm q ij.2]
    _ = _ := by rw [Finset.prod_const, card_indexPairs, ← pow_mul]

theorem collisionRationalMajorant_nonneg (n p : ℕ) (q : Fin n → ℝ) :
    0 ≤ collisionRationalMajorant n p q :=
  div_nonneg (norm_nonneg _) (pow_nonneg (by linarith [angularQuadratic_nonneg (flatConstrainedAngles q)]) _)

theorem collisionRationalMajorant_continuous (n p : ℕ) :
    Continuous (collisionRationalMajorant n p) := by
  have hV : Continuous (fun q : Fin n → ℝ =>
      edgeVandermondeSquared (complexAngles (flatConstrainedAngles q))) := by
    unfold edgeVandermondeSquared
    apply continuous_finsetProd
    intro ij _
    exact (((continuous_apply ij.1).comp
      ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n))).sub
      ((continuous_apply ij.2).comp
        ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n)))).pow 2
  exact hV.norm.div
    ((continuous_const.add ((angularQuadratic_continuous _).comp
      (flatConstrainedAngles_continuous n))).pow p)
    (fun q => pow_ne_zero _ (ne_of_gt (by linarith [angularQuadratic_nonneg (flatConstrainedAngles q)])))

theorem collisionRationalMajorant_bound {n p : ℕ} (hp : (n + 1).choose 2 ≤ p)
    (q : Fin n → ℝ) :
    collisionRationalMajorant n p q ≤
      (2 * ((n : ℝ) + 1)) ^ (2 * (n + 1).choose 2) *
        ((1 + ‖q‖ ^ 2) ^ (p - (n + 1).choose 2))⁻¹ := by
  let m := (n + 1).choose 2
  let A : ℝ := 1 + ‖q‖ ^ 2
  let C : ℝ := (2 * ((n : ℝ) + 1)) ^ (2 * m)
  have hA : 0 < A := by dsimp [A]; positivity
  have hV : ‖edgeVandermondeSquared (complexAngles (flatConstrainedAngles q))‖ ≤ C * A ^ m := by
    calc
      ‖edgeVandermondeSquared (complexAngles (flatConstrainedAngles q))‖ ≤
          (2 * ‖flatConstrainedAngles q‖) ^ (2 * m) := edgeVandermondeSquared_norm_bound _
      _ ≤ (2 * (((n : ℝ) + 1) * ‖q‖)) ^ (2 * m) :=
        pow_le_pow_left₀ (by positivity) (by linarith [flatConstrainedAngles_norm_le q]) _
      _ = C * (‖q‖ ^ 2) ^ m := by dsimp [C]; rw [← mul_assoc, mul_pow, pow_mul ‖q‖ 2 m]
      _ ≤ C * A ^ m := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
        exact pow_le_pow_left₀ (sq_nonneg _) (by dsimp [A]; linarith) _
  have hden : A ^ p ≤ (1 + angularQuadratic (flatConstrainedAngles q)) ^ p :=
    pow_le_pow_left₀ hA.le (by dsimp [A]; linarith [flatConstrainedAngles_quadratic_lower q]) _
  calc
    collisionRationalMajorant n p q ≤ (C * A ^ m) / A ^ p := by
      exact div_le_div₀ (by dsimp [C]; positivity) hV (pow_pos hA _) hden
    _ = C * (A ^ (p - m))⁻¹ := by
      have he : p = m + (p - m) := by dsimp [m]; omega
      nth_rw 1 [he]
      rw [pow_add]
      field_simp
    _ = _ := rfl

/-- The full constrained rational majorant is integrable at infinity
and at the collision, in the original independent-coordinate measure. -/
theorem collisionRationalMajorant_integrable {n p : ℕ}
    (hbudget : n + 2 * (n + 1).choose 2 < 2 * p) :
    Integrable (collisionRationalMajorant n p) volume := by
  have hp : (n + 1).choose 2 ≤ p := by omega
  let k := p - (n + 1).choose 2
  have hk : n < 2 * k := by dsimp [k]; omega
  have hdim : (Module.finrank ℝ (Fin n → ℝ) : ℝ) < 2 * (k : ℝ) := by
    simp only [Module.finrank_pi, Fintype.card_fin]
    exact_mod_cast hk
  have hbase : Integrable (fun q : Fin n → ℝ => ((1 + ‖q‖ ^ 2) ^ k)⁻¹) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Fin n → ℝ))) hdim
    convert h using 1
    funext q
    rw [show -(2 * (k : ℝ)) / 2 = -(k : ℝ) by ring,
      Real.rpow_neg (by positivity : 0 ≤ 1 + ‖q‖ ^ 2), Real.rpow_natCast]
  apply (hbase.const_mul ((2 * ((n : ℝ) + 1)) ^ (2 * (n + 1).choose 2))).mono'
    (collisionRationalMajorant_continuous n p).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    rw [Real.norm_of_nonneg (collisionRationalMajorant_nonneg n p q)]
    exact collisionRationalMajorant_bound hp q

end
end IsingBulk.AnisoF002.RegularTail.C03
