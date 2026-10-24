import IsingBulk.Anisotropic.PhysicalField.FiniteTilt

namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open scoped BigOperators

abbrev SpinConfig (n : ℕ) := Fin (n+1) → Bool

def spinValue {n : ℕ} (ω : SpinConfig n) (i : Fin (n+1)) : ℝ := if ω i then 1 else -1

/-- A finite marginal of the physical plus state. Coordinate 0 records the
observed spin; the remaining coordinates record the finitely perturbed sites.
Repeated physical sites are represented by equal coordinates on the support. -/
structure FiniteSpinLaw (n : ℕ) where
  weight : SpinConfig n → ℝ
  nonneg : ∀ ω, 0≤weight ω
  normalized : ∑ ω, weight ω=1

def FiniteSpinLaw.magnetization {n : ℕ} (P : FiniteSpinLaw n) (β h : ℝ) : ℝ :=
  tiltedMean β P.weight (fun ω => spinValue ω 0) (fun ω => ∑ i : Fin n, spinValue ω i.succ) h

def FiniteSpinLaw.centerMean {n : ℕ} (P : FiniteSpinLaw n) : ℝ :=
  mean P.weight (fun ω => spinValue ω 0)

def FiniteSpinLaw.siteCovariance {n : ℕ} (P : FiniteSpinLaw n) (i : Fin n) : ℝ :=
  covariance P.weight (fun ω => spinValue ω 0) (fun ω => spinValue ω i.succ)

theorem FiniteSpinLaw.magnetization_zero {n : ℕ} (P : FiniteSpinLaw n) (β : ℝ) :
    P.magnetization β 0=P.centerMean :=
  tiltedMean_zero β P.weight _ _ P.normalized

theorem FiniteSpinLaw.magnetization_derivative {n : ℕ} (P : FiniteSpinLaw n) (β : ℝ) :
    HasDerivAt (P.magnetization β) (β*∑ i, P.siteCovariance i) 0 :=
  tiltedMean_sum_hasDerivAt_zero β P.weight _ _ P.normalized

end
end IsingBulk.Anisotropic.PhysicalField
