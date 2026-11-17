import IsingBulk.AnisoF002.C03.PhysicalFiniteResidue
import IsingBulk.First.AnnulusProduct

/-!
# The actual collision-filled residue and its unit-circle deformation

F002's own unsquared dispersion subtraction cancels every reciprocal
angular Schur denominator.  The resulting finite density is analytic on
the whole common annulus, including all reciprocal-angle collisions.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
  IsingBulk.AnisoF002.Isotropic
open Set Filter Metric
open scoped Topology BigOperators

theorem annular_quadratic_cleared {B C : ℝ} {y R : ℂ} (hy : y ≠ 0)
    (hR : R ^ 2 - 2 * physicalAnnularW B C y * R + 1 = 0) :
    (1 : ℂ) * y * (R ^ 2 + 1) - 2 * (C : ℂ) * y * R +
      (B : ℂ) * (y ^ 2 + 1) * R = 0 := by
  unfold physicalAnnularW at hR
  field_simp at hR
  linear_combination hR

/-- The filled residue retains both site powers, all one-body factors, and
every F002 canceled pair, with the original inverse-sinh normalization. -/
def latticeFilledResidue {N : ℕ} (B S : ℂ) (v : LatticeSite)
    (R y : Fin N → ℂ) : ℂ :=
  coordinateProduct R ^ v.1.natAbs *
    (coordinateProduct y ^ v.2.natAbs * (coordinateProduct y)⁻¹) *
    (∏ i, 2 * R i / (S * (1 - R i ^ 2))) *
    ∏ ij ∈ indexPairs N, canceledPair B (R ij.1) (R ij.2) (y ij.1) (y ij.2)

theorem latticeResidueDensity_eq_filled {N : ℕ} {B C : ℝ} (S : ℂ)
    (v : LatticeSite) (R y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (hy1 : ∀ i, ‖y i‖ < 1)
    (hR : ∀ i, ‖R i‖ < 1 ∧
      R i ^ 2 - 2 * physicalAnnularW B C (y i) * R i + 1 = 0) :
    latticeResidueDensity S v R y = latticeFilledResidue (B : ℂ) S v R y := by
  have hp (i j : Fin N) : First.pairKernel (R i) (R j) * First.pairKernel (y i) (y j) =
      canceledPair (B : ℂ) (R i) (R j) (y i) (y j) := by
    simpa only [div_one, schur, First.pairKernel] using schur_pair_eq_canceled (by norm_num : (1 : ℂ) ≠ 0)
      (hy i) (hy j) (pair_root_denominator_ne_zero (hR i).1 (hR j).1)
      (pair_root_denominator_ne_zero (hy1 i) (hy1 j))
      (annular_quadratic_cleared (hy i) (hR i).2)
      (annular_quadratic_cleared (hy j) (hR j).2)
  have hpair : First.pairProduct R * First.pairProduct y =
      ∏ ij ∈ indexPairs N, canceledPair (B : ℂ) (R ij.1) (R ij.2) (y ij.1) (y ij.2) := by
    rw [prod_indexPairs_eq_nested (fun i j => canceledPair (B : ℂ) (R i) (R j) (y i) (y j))]
    unfold First.pairProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => hp i j)
  unfold latticeResidueDensity latticeResidueNumerator latticeFilledResidue
  simp only [pow_two]
  rw [← hpair]
  ring

theorem latticeFilledResidue_analyticAt {N : ℕ} {B S : ℂ} (hS : S ≠ 0)
    (v : LatticeSite) {R : ℂ → ℂ} {y : Fin N → ℂ}
    (hy : ∀ i, y i ≠ 0) (hR : ∀ i, AnalyticAt ℂ R (y i))
    (hRn : ∀ i, ‖R (y i)‖ < 1) :
    AnalyticAt ℂ (fun w : Fin N → ℂ => latticeFilledResidue B S v (fun i => R (w i)) w) y := by
  have ha (i : Fin N) : AnalyticAt ℂ (fun w : Fin N → ℂ => w i) y :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _
  have hb (i : Fin N) : AnalyticAt ℂ (fun w : Fin N → ℂ => R (w i)) y :=
    (hR i).comp (f := fun w : Fin N → ℂ => w i) (ha i)
  have hX := Finset.univ.analyticAt_fun_prod (fun i _ => hb i)
  have hY := Finset.univ.analyticAt_fun_prod (fun i _ => ha i)
  have hY0 : coordinateProduct y ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy i)
  have hden (i j : Fin N) := pair_root_denominator_ne_zero (hRn i) (hRn j)
  unfold latticeFilledResidue coordinateProduct
  apply (((hX.pow _).mul ((hY.pow _).mul (hY.inv hY0))).mul ?_).mul ?_
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (hb i)).div
      (analyticAt_const.mul (analyticAt_const.sub ((hb i).pow 2)))
      (mul_ne_zero hS (by simpa only [pow_two] using hden i i))
  · apply (indexPairs N).analyticAt_fun_prod
    intro ij _
    unfold canceledPair
    exact (((analyticAt_const.mul (((ha ij.1).sub (ha ij.2)).pow 2)).mul (hb ij.1)).mul
      (hb ij.2)).div
      (((ha ij.1).mul (ha ij.2)).mul
        ((analyticAt_const.sub ((hb ij.1).mul (hb ij.2))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy ij.1) (hy ij.2)) (pow_ne_zero _ (hden ij.1 ij.2)))

/-- A genuine finite deformation of the original physical lattice contour
to the unit angular torus.  The reciprocal-angle poles have been filled by
the independently proved F002 subtraction identity. -/
theorem literal_lattice_coefficient_eq_filled_unit {N : ℕ} {lam t r q : ℝ}
    (ht : 0 < t) (hr : ContourAnnulus lam (t : ℂ) r) (hqr : q < r)
    (hroot : ∀ y : ℂ, r ≤ ‖y‖ → ‖y‖ ≤ 1 →
      AnalyticAt ℂ (physicalAnnularRoot (realB lam t) (realC lam t)) y ∧
      physicalAnnularRoot (realB lam t) (realC lam t) y ≠ 0 ∧
      ‖physicalAnnularRoot (realB lam t) (realC lam t) y‖ < q ∧
      physicalAnnularRoot (realB lam t) (realC lam t) y ^ 2 -
        2 * physicalAnnularW (realB lam t) (realC lam t) y *
          physicalAnnularRoot (realB lam t) (realC lam t) y + 1 = 0)
    (v : LatticeSite) :
    literalLatticeCoefficientAtRadius N r lam (t : ℂ) v =
      (N.factorial : ℂ)⁻¹ * multiCircleIntegral 1 N (fun y =>
        latticeFilledResidue (realB lam t : ℂ) (Real.sinh t : ℂ) v
          (fun i => physicalAnnularRoot (realB lam t) (realC lam t) (y i)) y) := by
  let R := physicalAnnularRoot (realB lam t) (realC lam t)
  have hS : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
  unfold literalLatticeCoefficientAtRadius
  congr 1
  calc
    _ = multiCircleIntegral r N (fun y =>
        latticeFilledResidue (realB lam t : ℂ) (Real.sinh t : ℂ) v (fun i => R (y i)) y) := by
      apply multiCircleIntegral_congr hr.1.le N
      intro y hy
      have hh (i : Fin N) := hroot (y i) (hy i).ge ((hy i).le.trans hr.2.1.le)
      rw [literal_lattice_inner_residue ht hr.1 hr.2.1 v (fun i => R (y i)) y
        (fun i => ⟨(hh i).2.1, (hh i).2.2.1.trans hqr, (hh i).2.2.2⟩)]
      exact latticeResidueDensity_eq_filled _ v _ y
        (fun i => norm_ne_zero_iff.mp ((hy i).trans_ne hr.1.ne'))
        (fun i => (hy i).trans_lt hr.2.1)
        (fun i => ⟨(hh i).2.2.1.trans (hqr.trans hr.2.1), (hh i).2.2.2⟩)
    _ = _ := by
      symm
      apply multiCircleIntegral_radius_eq N hr.1 hr.2.1.le
      intro y hy
      have hh (i : Fin N) := hroot (y i) (hy i).1 (hy i).2
      exact (latticeFilledResidue_analyticAt hS v
        (fun i => norm_pos_iff.mp (hr.1.trans_le (hy i).1))
        (fun i => (hh i).1) (fun i => (hh i).2.2.1.trans (hqr.trans hr.2.1))).differentiableAt

end
end IsingBulk.AnisoF002.RegularTail.C03
