import IsingBulk.AnisoF002.C03.PhysicalFilledResidue
import IsingBulk.AnisoF002.C03.PhysicalLatticeReflection

/-!
# Exact original finite lattice coefficient from the actual contour

All factorials, angular Jacobians, square-root powers and signed Fourier
indices are retained.  The one actual radius is constructed before N and
the lattice site; no physical finite-coefficient equality is an assumption.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
  IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

theorem multiAngleIntegral_const_mul_f002 (N : ℕ) (a : ℂ) (f : (Fin N → ℝ) → ℂ) :
    multiAngleIntegral N (fun q => a * f q) = a * multiAngleIntegral N f := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [multiAngleIntegral, intervalIntegral.integral_const_mul]
    exact ih _

theorem positive_sqrt_product_eq_sinh_sqrt_ratio {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) :
    Real.sqrt (realProduct lam t) = Real.sinh t * Real.sqrt (realB lam t) := by
  have hS := Real.sinh_pos_iff.mpr ht
  have he : realProduct lam t = Real.sinh t ^ 2 * realB lam t := by
    unfold realProduct realB
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hS]

theorem unit_angle_coordinate_product {N : ℕ} (q : Fin N → ℝ) :
    coordinateProduct (angleTuple 1 q) = Complex.exp ((∑ i, (q i : ℂ)) * Complex.I) := by
  simp only [coordinateProduct, angleTuple, anglePoint, circleMap, Complex.ofReal_one,
    one_mul, zero_add, ← Complex.exp_sum, ← Finset.sum_mul]

theorem unit_angle_coordinate_power {N : ℕ} (q : Fin N → ℝ) (k : ℕ) :
    coordinateProduct (angleTuple 1 q) ^ k =
      Complex.exp (Complex.I * (k : ℂ) * ∑ i, (q i : ℂ)) := by
  rw [unit_angle_coordinate_product, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem unit_angle_jacobian {N : ℕ} (q : Fin N → ℝ) :
    angleProductJacobian 1 q = coordinateProduct (angleTuple 1 q) *
      ((2 * (Real.pi : ℂ))⁻¹) ^ N := by
  simp only [angleProductJacobian, angleJacobian, div_eq_mul_inv, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, coordinateProduct, angleTuple]

theorem filled_unit_numerator_normalization {N : ℕ} {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hp : realProduct lam t ≠ 1) (q : Fin N → ℝ) :
    let R : Fin N → ℂ := fun i => physicalAnnularRoot (realB lam t) (realC lam t) (angleTuple 1 q i)
    (Real.sqrt (realProduct lam t) : ℂ) ^ N *
      (∏ i, 2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) *
      (∏ ij ∈ indexPairs N, canceledPair (realB lam t : ℂ)
        (R ij.1) (R ij.2) (angleTuple 1 q ij.1) (angleTuple 1 q ij.2)) =
      (angularWeight (realB lam t) (realC lam t) q : ℂ) := by
  intro R
  have hR (i : Fin N) : R i = spectralSmallRootF002 lam (t : ℂ) (q i) := by
    rw [canonical_root_eq_published_real hlam ht hp]
    exact physicalAnnularRoot_unit_angle (realB_pos_f002 hlam ht).le
      (published_real_dispersion_gap_f002 hlam ht hp) (q i)
  have hy (i : Fin N) : angleTuple 1 q i = Complex.exp ((q i : ℂ) * Complex.I) := by
    simp only [angleTuple, anglePoint, circleMap, Complex.ofReal_one, one_mul, zero_add]
  have hS : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
  have hsqrt : (Real.sqrt (realProduct lam t) : ℂ) =
      (Real.sinh t : ℂ) * (Real.sqrt (realB lam t) : ℂ) := by
    exact_mod_cast positive_sqrt_product_eq_sinh_sqrt_ratio hlam ht
  have hi (i : Fin N) : (Real.sqrt (realProduct lam t) : ℂ) *
      (2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) =
      (Real.sqrt (realB lam t) : ℂ) * (2 * R i / (1 - R i ^ 2)) := by
    rw [hsqrt]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp
  have hprod : (Real.sqrt (realProduct lam t) : ℂ) ^ N *
      (∏ i, 2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) =
      (Real.sqrt (realB lam t) : ℂ) ^ N * (∏ i, 2 * R i / (1 - R i ^ 2)) := by
    calc
      _ = ∏ i : Fin N, (Real.sqrt (realProduct lam t) : ℂ) *
          (2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin N, (Real.sqrt (realB lam t) : ℂ) * (2 * R i / (1 - R i ^ 2)) :=
        Finset.prod_congr rfl (fun i _ => hi i)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, ← canonical_numerator_eq_published_real hlam ht hp q]
  unfold fullRootNumeratorF002 spectralOneBodyF002 spectralCanceledPairF002
  have hB : spectralT lam (t : ℂ) / spectralS (t : ℂ) = (realB lam t : ℂ) :=
    spectralRatio_real_f002 lam t
  simp only [hR, hy, hB]

theorem filled_unit_angular_integrand {N : ℕ} {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hp : realProduct lam t ≠ 1)
    (v : LatticeSite) (q : Fin N → ℝ) :
    (Real.sqrt (realProduct lam t) : ℂ) ^ N *
      (angleProductJacobian 1 q *
        latticeFilledResidue (realB lam t : ℂ) (Real.sinh t : ℂ) v
          (fun i => physicalAnnularRoot (realB lam t) (realC lam t) (angleTuple 1 q i))
          (angleTuple 1 q)) =
      ((2 * (Real.pi : ℂ))⁻¹) ^ N *
        (((angularWeight (realB lam t) (realC lam t) q *
          rootProduct (realB lam t) (realC lam t) q ^ v.1.natAbs : ℝ) : ℂ) *
          Complex.exp (Complex.I * (v.2.natAbs : ℂ) * ∑ i, (q i : ℂ))) := by
  let R : Fin N → ℂ := fun i => physicalAnnularRoot (realB lam t) (realC lam t) (angleTuple 1 q i)
  have hroot (i : Fin N) : R i = (FormFactors.root (realB lam t) (realC lam t) (q i) : ℂ) :=
    physicalAnnularRoot_unit_angle (realB_pos_f002 hlam ht).le
      (published_real_dispersion_gap_f002 hlam ht hp) (q i)
  have hprod : coordinateProduct R = (rootProduct (realB lam t) (realC lam t) q : ℂ) := by
    simp only [coordinateProduct, rootProduct, Complex.ofReal_prod, hroot]
  have hY : coordinateProduct (angleTuple 1 q) ≠ 0 := by
    rw [unit_angle_coordinate_product]
    exact Complex.exp_ne_zero _
  have hnum := filled_unit_numerator_normalization hlam ht hp q
  change (Real.sqrt (realProduct lam t) : ℂ) ^ N *
    (∏ i, 2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) *
    (∏ ij ∈ indexPairs N, canceledPair (realB lam t : ℂ)
      (R ij.1) (R ij.2) (angleTuple 1 q ij.1) (angleTuple 1 q ij.2)) = _ at hnum
  rw [unit_angle_jacobian]
  change _ * (_ * latticeFilledResidue _ _ v R _) = _
  unfold latticeFilledResidue
  calc
    _ = ((2 * (Real.pi : ℂ))⁻¹) ^ N *
        (coordinateProduct R ^ v.1.natAbs * coordinateProduct (angleTuple 1 q) ^ v.2.natAbs) *
        ((Real.sqrt (realProduct lam t) : ℂ) ^ N *
          (∏ i, 2 * R i / ((Real.sinh t : ℂ) * (1 - R i ^ 2))) *
          ∏ ij ∈ indexPairs N, canceledPair (realB lam t : ℂ)
            (R ij.1) (R ij.2) (angleTuple 1 q ij.1) (angleTuple 1 q ij.2)) := by
      field_simp
    _ = _ := by
      rw [hnum, hprod, unit_angle_coordinate_power]
      push_cast
      ring

end
end IsingBulk.AnisoF002.RegularTail.C03
