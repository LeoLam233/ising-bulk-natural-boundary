import IsingBulk.AnisoF002.C03.PhysicalRegularTail
import IsingBulk.AnisoF002.Geometry.CanonicalRootPhysical
import IsingBulk.Anisotropic.FormFactors.PublishedRealInput

/-!
# Literal published real form factors and the canonical physical numerator

Both positive noncritical real intervals use the same positive decaying
canonical root.  The exact positive real square root is retained through
all N one-body factors and every pair; its resulting power is precisely
the published B^(N²/2).  Only literal historical physical definitions are
referenced, and no historical physical-identification theorem is used.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

theorem realB_pos_f002 {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    0 < realB lam x :=
  div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam hx)) (Real.sinh_pos_iff.mpr hx)

theorem spectralRatio_real_f002 (lam x : ℝ) :
    spectralRatioF002 lam (x : ℂ) = (realB lam x : ℂ) := by
  simp only [spectralRatioF002, realB, spectralT, spectralS,
    ← Complex.ofReal_mul, ← Complex.ofReal_sinh, Complex.ofReal_div]

theorem realSpectralW_eq_published (lam x q : ℝ) :
    positiveRealSpectralW lam x q = realC lam x - realB lam x * Real.cos q := by
  unfold positiveRealSpectralW realC realB
  ring

theorem published_real_dispersion_gap_f002 {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    1 < realC lam x - realB lam x := by
  have h := positiveRealSpectralW_gt_one hlam hx hp 0
  simpa only [realSpectralW_eq_published, Real.cos_zero, mul_one] using h

theorem published_real_gamma_pos_f002 {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : ℝ) :
    0 < FormFactors.gamma (realB lam x) (realC lam x) q := by
  apply Real.arcosh_pos
  rw [← realSpectralW_eq_published]
  exact positiveRealSpectralW_gt_one hlam hx hp q

theorem canonical_root_eq_published_real {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : ℝ) :
    spectralSmallRootF002 lam (x : ℂ) q =
      (FormFactors.root (realB lam x) (realC lam x) q : ℂ) := by
  rw [spectralSmallRootF002_physical hlam hx hp q, realSpectralW_eq_published]
  rfl

theorem canonical_root_eq_published_phase {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : ℝ) :
    spectralSmallRootF002 lam (x : ℂ) q =
      Complex.exp (-(FormFactors.gamma (realB lam x) (realC lam x) q : ℂ)) := by
  rw [canonical_root_eq_published_real hlam hx hp q]
  simp only [FormFactors.root, Complex.ofReal_exp, Complex.ofReal_neg]

theorem sqrt_power_eq_published_anisotropy (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    Real.sqrt B ^ (N ^ 2) = anisotropyPower N B := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hB]
  unfold anisotropyPower
  congr 1
  push_cast
  ring

theorem prod_indexPairs_eq_nested {R : Type*} [CommMonoid R] {N : ℕ}
    (f : Fin N → Fin N → R) :
    (∏ ij ∈ indexPairs N, f ij.1 ij.2) =
      ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  rw [indexPairs, Finset.prod_filter, Finset.prod_product]
  simp only [Finset.prod_filter]

/-- Exact finite physical numerator, with no altered particle exponent. -/
theorem canonical_numerator_eq_published_real {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : Fin N → ℝ) :
    fullRootNumeratorF002 lam (x : ℂ) (Real.sqrt (realB lam x) : ℂ) q =
      (FormFactors.angularWeight (realB lam x) (realC lam x) q : ℂ) := by
  have hB := realB_pos_f002 hlam hx
  have hb : (Real.sqrt (realB lam x) : ℂ) ^ 2 = spectralT lam (x : ℂ) / spectralS (x : ℂ) := by
    change _ = spectralRatioF002 lam (x : ℂ)
    rw [spectralRatio_real_f002, ← Complex.ofReal_pow, Real.sq_sqrt hB.le]
  rw [fullRootNumeratorF002_log_branch lam (x : ℂ) (Real.sqrt (realB lam x) : ℂ) q
    (fun i => (FormFactors.gamma (realB lam x) (realC lam x) (q i) : ℂ))
    (fun i => canonical_root_eq_published_phase hlam hx hp (q i)) hb]
  rw [← Complex.ofReal_pow, sqrt_power_eq_published_anisotropy N hB.le]
  simp only [FormFactors.angularWeight, FormFactors.pairProduct, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_sinh, one_div,
    indexPairs, Finset.prod_filter, Finset.prod_product, apply_ite, Complex.ofReal_one]

/-- The literal full canonical density agrees with the published real
angular integrand, including its complete geometric site multiplier. -/
theorem canonical_density_eq_published_real {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : Fin N → ℝ) :
    canonicalAngularDensityF002 lam (x : ℂ) q =
      ((FormFactors.angularWeight (realB lam x) (realC lam x) q *
        ((1 + rootProduct (realB lam x) (realC lam x) q) /
          (1 - rootProduct (realB lam x) (realC lam x) q)) : ℝ) : ℂ) := by
  have hB := realB_pos_f002 hlam hx
  have hsqrt : Complex.sqrt (spectralRatioF002 lam (x : ℂ)) =
      (Real.sqrt (realB lam x) : ℂ) := by
    rw [spectralRatio_real_f002,
      Complex.sqrt_of_nonneg (by exact_mod_cast hB.le)]
    rfl
  rw [canonicalAngularDensityF002, hsqrt, canonical_numerator_eq_published_real hlam hx hp]
  simp only [canonical_root_eq_published_real hlam hx hp, rootProduct,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_prod]

end
end IsingBulk.AnisoF002.RegularTail.C03
