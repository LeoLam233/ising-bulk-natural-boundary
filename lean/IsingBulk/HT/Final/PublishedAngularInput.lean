import IsingBulk.HT.Contour.PhysicalAngular
import IsingBulk.HT.Final.PhysicalNormalization

/-! The precise external statistical-mechanical interface, stated in the
published angular variables rather than the double-contour variables.

The physical input in HT-1.0, equations (2.1)--(2.2), is the classical
odd-particle bulk expansion in Orrick et al. (2001), equations (1.9), (1.11),
(3.13), (3.17)--(3.20), and Boukraa et al. (2008), equations (3), (5)--(9).
The definitions below expose that input as a proposition, not as an axiom.

No contour equality, Fourier summation theorem, first singularity, tail
bound, natural boundary or analyticity certificate is imported here.
In particular, `RealFullBulkRepresentation` is a different interface:
identifying it with this one requires a proved angular/full-lattice/contour
bridge. A theorem conditional on this input remains conditional on the
statistical-mechanical form-factor representation. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.HT.Contour IsingBulk.Final
open scoped BigOperators

/-- Every positive odd particle number appears exactly once. The argument
`2*n` of the angular coefficient counts independent angles, so its particle
number is `2*n+1`. Convergence is not assumed in this definition. -/
def publishedAngularOddSeries (t : ℝ) : ℂ :=
  ∑' n : ℕ, physicalAngularCoefficient (2*n) t

/-- The exact beta-free physical bulk identity on the real HT interval.
This is the sole published physical input, not an internally proved theorem
about an independently defined infinite-volume Gibbs state. -/
def PublishedAngularBulkRepresentation (X : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 →
    X (x:ℂ) = interiorPrefactor (x:ℂ)*publishedAngularOddSeries x⁻¹

/-- The same external input for the susceptibility including physical beta. -/
def PublishedAngularSusceptibilityRepresentation (J : ℝ) (chi : ℂ → ℂ) : Prop :=
  PublishedAngularBulkRepresentation
    (fun s => chi s / inverseTemperatureBranch J s)

/-- The temperature factor is restored by algebra on the actual real HT
interval, without adding a complex analyticity hypothesis. -/
theorem publishedAngular_real_normalization {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PublishedAngularSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    chi (x:ℂ) = inverseTemperatureBranch J (x:ℂ) *
      interiorPrefactor (x:ℂ)*publishedAngularOddSeries x⁻¹ := by
  have hb0 := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa using hx) hJ).2
  have hid := (div_eq_iff hb0).mp (hrep x hx hx1)
  calc
    chi (x:ℂ) = (interiorPrefactor (x:ℂ)*publishedAngularOddSeries x⁻¹)*
        inverseTemperatureBranch J (x:ℂ) := hid
    _ = _ := by ring

end
end IsingBulk.HT.Final
