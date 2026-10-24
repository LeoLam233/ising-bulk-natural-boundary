import IsingBulk.Anisotropic.Geometry.AxisExchange
import IsingBulk.Anisotropic.FormFactors.RadiusIndependence
import IsingBulk.Anisotropic.FormFactors.ContourContinuity

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem sliceDispersion_axis_exchange {lam : ℝ} (hlam : lam≠0) (z x y : ℂ) :
    sliceDispersion (lam⁻¹) ((lam:ℂ)*z) x y=sliceDispersion lam z y x := by
  unfold sliceDispersion
  rw [spectralT_axis_exchange hlam,spectralA_axis_exchange hlam]
  exact dispersion_axis_exchange (spectralT lam z) (spectralS z) (spectralA lam z) x y

theorem contourAnnulus_axis_exchange {r lam : ℝ} {z : ℂ}
    (hlam : lam≠0) (h : ContourAnnulus lam z r) :
    ContourAnnulus (lam⁻¹) ((lam:ℂ)*z) r := by
  refine ⟨h.1,h.2.1,?_⟩
  intro x y hx hx1 hy hy1
  rw [sliceDispersion_axis_exchange hlam]
  exact h.2.2 y x hy hy1 hx hx1

theorem fullDensity_axis_exchange {N : ℕ} {lam : ℝ} (hlam : lam≠0)
    (z : ℂ) (x y : Fin N → ℂ) :
    fullDensity (lam⁻¹) ((lam:ℂ)*z) x y=fullDensity lam z y x := by
  unfold fullDensity commonDensity
  simp_rw [sliceDispersion_axis_exchange hlam]
  simp only [mul_comm,mul_left_comm,mul_assoc]

theorem unscaledFullCoefficientAtRadius_axis_exchange (N : ℕ) (hN : 0<N)
    {r lam : ℝ} {z : ℂ} (hlam : lam≠0) (hr : ContourAnnulus lam z r) :
    unscaledFullCoefficientAtRadius N r (lam⁻¹) ((lam:ℂ)*z)=
      unscaledFullCoefficientAtRadius N r lam z := by
  rw [unscaledFullCoefficientAtRadius_eq_box N hN (contourAnnulus_axis_exchange hlam hr),
    unscaledFullCoefficientAtRadius_eq_box N hN hr]
  congr 1
  have he (p : (Fin N → ℝ) × (Fin N → ℝ)) :
      doubleAngularDensityOf r (fullDensity (lam⁻¹) ((lam:ℂ)*z)) p=
        doubleAngularDensityOf r (fullDensity lam z) p.swap := by
    unfold doubleAngularDensityOf
    rw [fullDensity_axis_exchange hlam]
    dsimp only [Prod.swap]
    ring
  simp_rw [he]
  exact setIntegral_prod_swap (angleBox N) (angleBox N) (doubleAngularDensityOf r (fullDensity lam z))

theorem unscaledFullCoefficient_axis_exchange (N : ℕ) (hN : 0<N)
    {lam : ℝ} {z : ℂ} (hlam : lam≠0) (hz : z∉spectralSet lam) :
    unscaledFullCoefficient N (lam⁻¹) ((lam:ℂ)*z)=unscaledFullCoefficient N lam z := by
  have hr := contourRadius_valid hz
  have hz' : (lam:ℂ)*z∉spectralSet (lam⁻¹) := mt (mem_spectralSet_axis_exchange_iff hlam z).mp hz
  rw [unscaledFullCoefficient_eq_fixed_radius N hN hz' (contourAnnulus_axis_exchange hlam hr)]
  exact unscaledFullCoefficientAtRadius_axis_exchange N hN hlam hr

end
end IsingBulk.Anisotropic.FormFactors
