import IsingBulk.AnisoF002.C03.PhysicalAnnularRoot
import IsingBulk.AnisoF002.C03.PhysicalContourAnalytic
import IsingBulk.AnisoF002.C03.PhysicalLatticeDefinitions
import IsingBulk.First.NormalizedContour

/-!
# Finite Cauchy reduction of the original lattice contours

The actual reciprocal root is used in every residue.  The common radius is
fixed before both the particle number and lattice displacement.  No
historical physical contour or lattice-identification theorem is used.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
open Set Filter Metric
open scoped Topology BigOperators

theorem quadratic_dispersion_factor {S W R u : ℂ} (hu : u ≠ 0) (hR : R ≠ 0)
    (hp : R ^ 2 - 2 * W * R + 1 = 0) :
    S * (W - (u + u⁻¹) / 2) = S * (u - R) * (1 - u * R) / (2 * u * R) := by
  field_simp
  linear_combination -S * u * hp

theorem quadratic_dispersion_inverse {S W R u : ℂ} (hS : S ≠ 0)
    (hu : u ≠ 0) (hR : R ≠ 0) (hd : u - R ≠ 0) (hc : 1 - u * R ≠ 0)
    (hp : R ^ 2 - 2 * W * R + 1 = 0) :
    u⁻¹ * (S * (W - (u + u⁻¹) / 2))⁻¹ =
      (u - R)⁻¹ * (2 * R / (S * (1 - u * R))) := by
  rw [quadratic_dispersion_factor hu hR hp]
  field_simp

theorem physical_sliceDispersion_as_W {lam t : ℝ} (ht : 0 < t) (u y : ℂ) :
    sliceDispersion lam (t : ℂ) u y =
      (Real.sinh t : ℂ) * (physicalAnnularW (realB lam t) (realC lam t) y -
        (u + u⁻¹) / 2) := by
  have hS : (Real.sinh t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
  have hSc : Complex.sinh (t : ℂ) ≠ 0 := by simpa only [← Complex.ofReal_sinh] using hS
  simp only [sliceDispersion, dispersionPolynomial, spectralA, spectralS, spectralT,
    physicalAnnularW, realB, realC, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_cosh, Complex.ofReal_sinh]
  field_simp [hSc]
  ring

/-- The holomorphic numerator left after the N simple Cauchy kernels. -/
def latticeResidueNumerator {N : ℕ} (S : ℂ) (v : LatticeSite)
    (R y u : Fin N → ℂ) : ℂ :=
  coordinateProduct u ^ v.1.natAbs *
    (coordinateProduct y ^ v.2.natAbs * (coordinateProduct y)⁻¹) *
    First.pairProduct u * First.pairProduct y *
    ∏ i, 2 * R i / (S * (1 - u i * R i))

def latticeResidueDensity {N : ℕ} (S : ℂ) (v : LatticeSite)
    (R y : Fin N → ℂ) : ℂ := latticeResidueNumerator S v R y R

theorem latticeResidueNumerator_analyticAt {N : ℕ} {S : ℂ}
    (hS : S ≠ 0) (v : LatticeSite) (R y : Fin N → ℂ)
    {u : Fin N → ℂ} (hu : ∀ i, ‖u i‖ < 1) (hR : ∀ i, ‖R i‖ < 1) :
    AnalyticAt ℂ (latticeResidueNumerator S v R y) u := by
  have ha (i : Fin N) : AnalyticAt ℂ (fun w : Fin N → ℂ => w i) u :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _
  have hX := Finset.univ.analyticAt_fun_prod (fun i _ => ha i)
  have hP := literal_pairProduct_analyticAt ha
    (fun i j => pair_root_denominator_ne_zero (hu i) (hu j))
  unfold latticeResidueNumerator coordinateProduct
  apply ((((hX.pow _).mul analyticAt_const).mul hP).mul analyticAt_const).mul
  apply Finset.univ.analyticAt_fun_prod
  intro i _
  exact analyticAt_const.div
    (analyticAt_const.mul (analyticAt_const.sub ((ha i).mul analyticAt_const)))
    (mul_ne_zero hS (pair_root_denominator_ne_zero (hu i) (hR i)))

theorem literalLatticeDensity_eq_cauchy {N : ℕ} {lam t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hr1 : r < 1) (v : LatticeSite)
    (R y u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ = r)
    (hR : ∀ i, R i ≠ 0 ∧ ‖R i‖ < r ∧
      R i ^ 2 - 2 * physicalAnnularW (realB lam t) (realC lam t) (y i) * R i + 1 = 0) :
    literalLatticeDensity lam (t : ℂ) v u y =
      (∏ i, (u i - R i)⁻¹) * latticeResidueNumerator (Real.sinh t : ℂ) v R y u := by
  have hS : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
  have hi (i : Fin N) : (u i)⁻¹ * (sliceDispersion lam (t : ℂ) (u i) (y i))⁻¹ =
      (u i - R i)⁻¹ * (2 * R i / ((Real.sinh t : ℂ) * (1 - u i * R i))) := by
    rw [physical_sliceDispersion_as_W ht]
    apply quadratic_dispersion_inverse hS
      (norm_ne_zero_iff.mp ((hu i).trans_ne hr.ne')) (hR i).1
    · intro he
      have hn := congrArg norm (sub_eq_zero.mp he)
      rw [hu i] at hn
      exact (hR i).2.1.ne hn.symm
    · exact pair_root_denominator_ne_zero ((hu i).trans_lt hr1) ((hR i).2.1.trans hr1)
    · exact (hR i).2.2
  have hprod : (coordinateProduct u)⁻¹ *
      (∏ i, (sliceDispersion lam (t : ℂ) (u i) (y i))⁻¹) =
      (∏ i, (u i - R i)⁻¹) *
        ∏ i, 2 * R i / ((Real.sinh t : ℂ) * (1 - u i * R i)) := by
    rw [coordinateProduct, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun i _ => hi i), Finset.prod_mul_distrib]
  unfold literalLatticeDensity FormFactors.onsiteDensity FormFactors.commonDensity
    latticeResidueNumerator
  rw [mul_inv_rev]
  calc
    _ = coordinateProduct u ^ v.1.natAbs *
        (coordinateProduct y ^ v.2.natAbs * (coordinateProduct y)⁻¹) *
        First.pairProduct u * First.pairProduct y *
        ((coordinateProduct u)⁻¹ * ∏ i, (sliceDispersion lam (t : ℂ) (u i) (y i))⁻¹) := by ring
    _ = _ := by rw [hprod]; ring

/-- Actual finite Cauchy residues for arbitrary N and lattice site. -/
theorem literal_lattice_inner_residue {N : ℕ} {lam t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hr1 : r < 1) (v : LatticeSite)
    (R y : Fin N → ℂ)
    (hR : ∀ i, R i ≠ 0 ∧ ‖R i‖ < r ∧
      R i ^ 2 - 2 * physicalAnnularW (realB lam t) (realC lam t) (y i) * R i + 1 = 0) :
    multiCircleIntegral r N (fun u => literalLatticeDensity lam (t : ℂ) v u y) =
      latticeResidueDensity (Real.sinh t : ℂ) v R y := by
  have hS : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
  calc
    _ = multiCircleIntegral r N (fun u => (∏ i, (u i - R i)⁻¹) *
        latticeResidueNumerator (Real.sinh t : ℂ) v R y u) := by
      apply multiCircleIntegral_congr hr.le N
      intro u hu
      exact literalLatticeDensity_eq_cauchy ht hr hr1 v R y u hu hR
    _ = _ := by
      exact multiCircleIntegral_cauchy hr N _ R (fun i => (hR i).2.1)
        (fun u hu => (latticeResidueNumerator_analyticAt hS v R y
          (fun i => (hu i).trans_lt hr1) (fun i => (hR i).2.1.trans hr1)).differentiableAt)

end
end IsingBulk.AnisoF002.RegularTail.C03
