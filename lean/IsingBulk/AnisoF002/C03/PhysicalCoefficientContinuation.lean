import IsingBulk.AnisoF002.C03.PhysicalCanonicalDensity
import IsingBulk.AnisoF002.C03.PhysicalRealCoefficient
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Exact canonical-to-original coefficient continuation on both full domains

The actual filled angular integral is analytic through S=0.  The finite
positive-real identity therefore continues on each complete original
physical component.  No assumed complex form-factor equality and no
principal square-root power convention is used.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry
open scoped Topology BigOperators

theorem physical_real_square_root_product {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    spectralS (x : ℂ) * Complex.sqrt (spectralRatioF002 lam (x : ℂ)) =
      (Real.sqrt (realProduct lam x) : ℂ) := by
  have hS : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hB := realB_pos_f002 hlam hx
  have he : Real.sinh x ^ 2 * realB lam x = realProduct lam x := by
    unfold realB realProduct
    field_simp
  have hs : Real.sinh x * Real.sqrt (realB lam x) = Real.sqrt (realProduct lam x) := by
    calc
      _ = Real.sqrt (Real.sinh x ^ 2) * Real.sqrt (realB lam x) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hS]
      _ = Real.sqrt (Real.sinh x ^ 2 * realB lam x) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = _ := by rw [he]
  rw [spectralRatio_real_f002, Complex.sqrt_of_nonneg (by exact_mod_cast hB.le)]
  change (Complex.sinh (x : ℂ)) * (Real.sqrt (realB lam x) : ℂ) = _
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_mul, hs]

theorem physicalCanonicalCoefficient_eq_original_real (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    physicalCanonicalCoefficient lam n (x : ℂ) = unscaledFullCoefficient (n + 1) lam (x : ℂ) := by
  have he := canonical_coefficient_eq_original_real n hlam hx hp
  rw [canonical_coefficient_eq_physicalCanonical n (positive_real_not_mem_spectralSetF002 hlam hx hp),
    physical_real_square_root_product hlam hx] at he
  exact mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Physical.realProduct_pos hlam hx)).ne')) he

theorem analytic_eqOn_of_real_interval {f g : ℂ → ℂ} {U : Set ℂ} {a b : ℝ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U)
    (ha : (a : ℂ) ∈ U) (hab : a < b)
    (he : ∀ x ∈ Ioo a b, f (x : ℂ) = g (x : ℂ)) : EqOn f g U := by
  apply hf.eqOn_of_preconnected_of_mem_closure hg hU ha
  have ha' : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  have hm : Complex.ofReal '' Ioo a b ⊆ {z | f z = g z} \ {(a : ℂ)} := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨he x hx, ?_⟩
    intro hh
    exact (ne_of_gt hx.1) (Complex.ofReal_injective (mem_singleton_iff.mp hh))
  exact closure_mono hm (mem_closure_image Complex.continuous_ofReal.continuousAt ha')

theorem physicalCanonicalCoefficient_eq_original_high (n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) :
    EqOn (physicalCanonicalCoefficient lam n) (fun z => unscaledFullCoefficient (n + 1) lam z) (omegaH lam) := by
  let c := criticalPointF002 lam
  have hc : 0 < c := criticalPointF002_pos hlam
  apply analytic_eqOn_of_real_interval
    (fun z hz => physicalCanonicalCoefficient_analyticAt n (omegaHF002_subset_complement hlam hz))
    (fun z hz => literal_coefficient_analyticOnNhd (n + 1) (Nat.succ_pos n) lam z
      (omegaHF002_subset_complement hlam hz))
    (omegaHF002_isPreconnected hlam)
    (Physical.nonnegative_real_mem_high hlam (by linarith : 0 ≤ c / 2) (by dsimp [c]; linarith))
    (show c / 2 < c by linarith)
  intro x hx
  have hx0 : 0 < x := lt_trans (half_pos hc) hx.1
  exact physicalCanonicalCoefficient_eq_original_real n hlam hx0
    ((Physical.realProduct_lt_one_iff_lt_critical hlam hx0.le).mpr hx.2).ne

theorem physicalCanonicalCoefficient_eq_original_low (n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) :
    EqOn (physicalCanonicalCoefficient lam n) (fun z => unscaledFullCoefficient (n + 1) lam z) (omegaL lam) := by
  let c := criticalPointF002 lam
  have hc : 0 < c := criticalPointF002_pos hlam
  have ha : ((c + 1 : ℝ) : ℂ) ∈ omegaL lam :=
    (real_mem_omegaLF002_iff hlam).mpr (by linarith)
  apply analytic_eqOn_of_real_interval
    (fun z hz => physicalCanonicalCoefficient_analyticAt n (omegaLF002_subset_complement hlam hz))
    (fun z hz => literal_coefficient_analyticOnNhd (n + 1) (Nat.succ_pos n) lam z
      (omegaLF002_subset_complement hlam hz))
    (omegaLF002_isPreconnected hlam) ha (show c + 1 < c + 2 by linarith)
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hxc : criticalPointF002 lam < x := by change c < x; linarith [hx.1]
  exact physicalCanonicalCoefficient_eq_original_real n hlam hx0
    ((Physical.critical_lt_iff_realProduct_gt_one hlam hx0.le).mp hxc).ne'

theorem canonical_coefficient_eq_original_high (n : ℕ) {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaH lam) :
    canonicalAngularCoefficientF002 lam n z =
      (spectralS z * Complex.sqrt (spectralRatioF002 lam z)) ^ (n + 1) *
        unscaledFullCoefficient (n + 1) lam z := by
  rw [canonical_coefficient_eq_physicalCanonical n (omegaHF002_subset_complement hlam hz),
    physicalCanonicalCoefficient_eq_original_high n hlam hz]

theorem canonical_coefficient_eq_original_low (n : ℕ) {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaL lam) :
    canonicalAngularCoefficientF002 lam n z =
      (spectralS z * Complex.sqrt (spectralRatioF002 lam z)) ^ (n + 1) *
        unscaledFullCoefficient (n + 1) lam z := by
  rw [canonical_coefficient_eq_physicalCanonical n (omegaLF002_subset_complement hlam hz),
    physicalCanonicalCoefficient_eq_original_low n hlam hz]

end
end IsingBulk.AnisoF002.RegularTail.C03
