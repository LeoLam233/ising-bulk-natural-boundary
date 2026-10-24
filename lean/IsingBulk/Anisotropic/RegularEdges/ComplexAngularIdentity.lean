import IsingBulk.Anisotropic.FormFactors.FiniteHolomorphy
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularReal
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularHolomorphy
import IsingBulk.Anisotropic.Final.RealIntervalUniqueness
import IsingBulk.Anisotropic.Final.RealPrefactors
import IsingBulk.Anisotropic.Geometry.HighPunctured
import IsingBulk.Anisotropic.Geometry.Components

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open FormFactors IsingBulk.First IsingBulk.HT.Contour Set
open scoped BigOperators

theorem scaled_unscaledAngularCoefficient_real (n : ℕ) {lam x : ℝ}
    (hlam : 0<lam) (hx : 0<x) (hp : realProduct lam x≠1) :
    ((Real.sqrt (realProduct lam x))^(n+1):ℝ)*unscaledAngularCoefficient n lam (x:ℂ) =
      angularCoefficient n (realB lam x) (realC lam x) := by
  have hpoint (q : Fin (n+1) → ℝ) :
      (((Real.sqrt (realProduct lam x))^(n+1):ℝ):ℂ)*
        complexAngularDensity lam (x:ℂ) (fun i => (q i:ℂ)) =
        (angularWeight (realB lam x) (realC lam x) q *
          ((1+rootProduct (realB lam x) (realC lam x) q)/
            (1-rootProduct (realB lam x) (realC lam x) q)):ℝ) := by
    unfold complexAngularDensity
    rw [← mul_assoc,scaled_complexAngularWeight_real hlam hx hp]
    simp_rw [transferRoot_real hlam hx hp]
    simp only [rootProduct,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_prod]
  calc
    _ = ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
      multiAngleIntegral n (fun q => (((Real.sqrt (realProduct lam x))^(n+1):ℝ):ℂ)*
        complexAngularDensity lam (x:ℂ) (fun i => (physicalDependentAngles n q i:ℂ))) := by
      rw [physical_multiAngleIntegral_const_mul]
      unfold unscaledAngularCoefficient
      ring
    _ = _ := by simp_rw [hpoint]; rfl

theorem unscaledFullCoefficient_eq_angular_real (n : ℕ) {lam x : ℝ}
    (hlam : 0<lam) (hx : 0<x) (hp : realProduct lam x≠1) :
    unscaledFullCoefficient (n+1) lam (x:ℂ)=unscaledAngularCoefficient n lam (x:ℂ) := by
  have hp0 : 0<realProduct lam x := mul_pos (Real.sinh_pos_iff.mpr hx)
    (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero (n+1) (Real.sqrt_pos.mpr hp0).ne'))
  rw [scaled_unscaledFullCoefficient_eq_angular n hlam hx hp,
    scaled_unscaledAngularCoefficient_real n hlam hx hp]

theorem unscaledFullCoefficient_eq_angular_omegaH (n : ℕ) {lam : ℝ} (hlam : 0<lam) :
    EqOn (unscaledFullCoefficient (n+1) lam) (unscaledAngularCoefficient n lam) (omegaH lam\{0}) := by
  apply analytic_eqOn_of_real_interval
    (fun z hz => unscaledFullCoefficient_analyticOnNhd (n+1) (by omega) lam z
      (omegaH_subset_spectral_complement hlam hz.1))
    (fun z hz => unscaledAngularCoefficient_analyticAt n
      (omegaH_subset_spectral_complement hlam hz.1)
      (omegaH_spectralS_ne_zero hlam hz.1 hz.2))
    (omegaH_punctured_isPreconnected hlam) (criticalPoint_pos hlam)
  · intro x hx
    exact ⟨real_mem_omegaH_of_nonneg_lt_critical hlam hx.1.le hx.2,
      Complex.ofReal_ne_zero.mpr hx.1.ne'⟩
  · intro x hx
    apply unscaledFullCoefficient_eq_angular_real n hlam hx.1
    have hh := highRealRadicand_pos hlam hx.1.le hx.2
    intro he
    rw [he] at hh
    norm_num at hh

theorem unscaledFullCoefficient_eq_angular_omegaL (n : ℕ) {lam : ℝ} (hlam : 0<lam) :
    EqOn (unscaledFullCoefficient (n+1) lam) (unscaledAngularCoefficient n lam) (omegaL lam) := by
  apply analytic_eqOn_of_real_interval
    (fun z hz => unscaledFullCoefficient_analyticOnNhd (n+1) (by omega) lam z
      (omegaL_subset_spectral_complement hlam hz))
    (fun z hz => unscaledAngularCoefficient_analyticAt n
      (omegaL_subset_spectral_complement hlam hz)
      (sinh_ne_zero_of_re_pos (omegaL_re_pos hlam hz)))
    (omegaL_isPreconnected hlam) (show criticalPoint lam<criticalPoint lam+1 by linarith)
  · intro x hx
    exact (real_mem_omegaL_iff hlam x).mpr hx.1
  · intro x hx
    have hx0 := (criticalPoint_pos hlam).trans hx.1
    exact unscaledFullCoefficient_eq_angular_real n hlam hx0
      ((criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hx.1).ne'

end
end IsingBulk.Anisotropic.RegularEdges
