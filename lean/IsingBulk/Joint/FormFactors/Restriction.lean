import IsingBulk.Joint.FormFactors.RadiusIndependence
import IsingBulk.Joint.FormFactors.Normalized
import IsingBulk.Anisotropic.FormFactors.RadiusIndependence

/-! Exact restriction of the same double-contour integrals. Equality is proved
at every actual particle number, not inferred from an ambient boundary claim. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section

@[simp] theorem dispersion_ratioSlice (lam : ℝ) (z x y : ℂ) :
    dispersion (ratioSlice lam z) x y = Anisotropic.FormFactors.sliceDispersion lam z x y := rfl

@[simp] theorem contourAnnulus_ratioSlice (lam r : ℝ) (z : ℂ) :
    ContourAnnulus (ratioSlice lam z) r ↔ Anisotropic.FormFactors.ContourAnnulus lam z r := Iff.rfl

@[simp] theorem fullDensity_ratioSlice {N : ℕ} (lam : ℝ) (z : ℂ) (x y : Fin N → ℂ) :
    fullDensity (ratioSlice lam z) x y = Anisotropic.FormFactors.fullDensity lam z x y := rfl

@[simp] theorem unscaledFullCoefficientAtRadius_ratioSlice (N : ℕ) (r lam : ℝ) (z : ℂ) :
    unscaledFullCoefficientAtRadius N r (ratioSlice lam z) =
      Anisotropic.FormFactors.unscaledFullCoefficientAtRadius N r lam z := rfl

theorem unscaledFullCoefficient_ratioSlice (N : ℕ) (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (hz : z ∉ Anisotropic.spectralSet lam) :
    unscaledFullCoefficient N (ratioSlice lam z) =
      Anisotropic.FormFactors.unscaledFullCoefficient N lam z := by
  have hK : ratioSlice lam z ∉ spectralSet := hz
  have ha := contourRadius_valid hK
  change Anisotropic.FormFactors.unscaledFullCoefficientAtRadius N
    (contourRadius (ratioSlice lam z)) lam z = _
  exact (Anisotropic.FormFactors.unscaledFullCoefficient_eq_fixed_radius N hN hz ha).symm

@[simp] theorem p_ratioSlice (lam : ℝ) (z : ℂ) :
    p (ratioSlice lam z) = Anisotropic.spectralProduct lam z := rfl
end
end IsingBulk.Joint.FormFactors
