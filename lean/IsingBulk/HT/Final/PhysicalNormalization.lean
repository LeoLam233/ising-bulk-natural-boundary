import IsingBulk.First.NormalizationDerivatives
import IsingBulk.Final.MagnetizationBoundary
import IsingBulk.Final.InverseTemperature

/-! High-temperature normalization, using the existing literal all-N contour
objects. This file does not identify the LT and HT susceptibilities. The
physical representation below is an explicit contour-normalized real-domain
interface, not a proof of the statistical-mechanical identity or of a natural
boundary. It is not literally the published angular identity: attaching the
two requires the all-particle angular/full-lattice/contour bridge. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Final Set
open scoped BigOperators

/-- Odd full-site coefficient C_(2n+1), at a fixed contour radius. -/
def oddFullCoefficient (n : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  standardFormFactor (2*n+1) r t

/-- Full odd-particle series; convergence is a separate mathematical claim. -/
def fixedOddFullSeries (r : ℝ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, oddFullCoefficient n r t

/-- P_H(s), with the principal fourth root positive on the physical interval. -/
def interiorPrefactor (s : ℂ) : ℂ := (1-s^4)^(1/4:ℂ)/s

/-- Q_H(t), the exterior-coordinate representation of exactly the same factor. -/
def exteriorPrefactor (t : ℂ) : ℂ := t*magnetizationSquared t

theorem interiorPrefactor_inv (t : ℂ) :
    interiorPrefactor (t⁻¹) = exteriorPrefactor t := by
  simp only [interiorPrefactor, exteriorPrefactor, magnetizationSquared,
    inv_pow, div_inv_eq_mul, mul_comm]

theorem exteriorPrefactor_analyticOn :
    AnalyticOnNhd ℂ exteriorPrefactor {t : ℂ | 1 < ‖t‖} := by
  intro t ht
  exact analyticAt_id.mul (magnetizationSquared_analyticOn_exterior t ht)

theorem exteriorPrefactor_regular_at_unit_nonaxis {t : ℂ}
    (ht : ‖t‖=1) (hfour : t^4 ≠ 1) :
    AnalyticAt ℂ exteriorPrefactor t ∧ exteriorPrefactor t ≠ 0 := by
  have ht0 : t ≠ 0 := norm_ne_zero_iff.mp (by rw [ht]; norm_num)
  exact ⟨analyticAt_id.mul (magnetizationSquared_analyticAt_unit_nonaxis ht hfour),
    mul_ne_zero ht0 (magnetizationSquared_ne_zero_at_unit_nonaxis ht hfour)⟩

/-- The source manuscript's beta-free full lattice observable in t=1/s. -/
def fixedNormalizedBulk (r : ℝ) (t : ℂ) : ℂ :=
  exteriorPrefactor t * fixedOddFullSeries r t

/-- Contour-normalized real high-temperature full bulk interface: all odd
positive particle numbers, every sufficiently large interior contour radius,
and beta-free susceptibility. This is not itself the published angular input;
deriving it from that input requires the genuine full-lattice identity.
It is not LT E1 or LT E2. -/
def RealFullBulkRepresentation (X : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧
    ∀ r : ℝ, r₀ < r → r < 1 →
      Summable (fun n : ℕ => oddFullCoefficient n r ((x:ℂ)⁻¹)) ∧
      X (x:ℂ) = interiorPrefactor (x:ℂ)*fixedOddFullSeries r ((x:ℂ)⁻¹)

/-- Physical chi=beta*X normalization. This is only an input predicate. -/
def PhysicalSusceptibilityRepresentation (J : ℝ) (chi : ℂ → ℂ) : Prop :=
  RealFullBulkRepresentation (fun s => chi s / inverseTemperatureBranch J s)

/-- All-N LT normalization specializes to the actual odd full-site contour,
with its geometric margin exposed and with no change to the integrand. -/
theorem oddFullCoefficient_iteratedDeriv (n j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {t : ℂ}
    (hm : r⁻¹-r < (sourceS t).im) :
    iteratedDeriv j (oddFullCoefficient n r) t =
      iteratedDeriv j (onsiteFormFactor (2*n+1) r) t +
      2*iteratedDeriv j (doubleFormFactor (2*n+1) r) t :=
  standardFormFactor_iteratedDeriv_eq (2*n+1) (by omega) j hr hr1 hm

/-- Recover chi from its beta-free physical interface on 0<s<1. This theorem
has an explicit representation hypothesis and asserts no boundary conclusion. -/
theorem physical_real_normalization {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PhysicalSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ ∀ r : ℝ, r₀ < r → r < 1 →
      Summable (fun n : ℕ => oddFullCoefficient n r ((x:ℂ)⁻¹)) ∧
      chi (x:ℂ) = inverseTemperatureBranch J (x:ℂ) *
        interiorPrefactor (x:ℂ)*fixedOddFullSeries r ((x:ℂ)⁻¹) := by
  obtain ⟨r₀,hr₀,hr₀1,h⟩ := hrep x hx hx1
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hr1
  obtain ⟨hs,he⟩ := h r hr hr1
  have hb0 := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa using hx) hJ).2
  refine ⟨hs,?_⟩
  have hid := (div_eq_iff hb0).mp he
  calc
    chi (x:ℂ) = (interiorPrefactor (x:ℂ)*fixedOddFullSeries r ((x:ℂ)⁻¹))*
        inverseTemperatureBranch J (x:ℂ) := hid
    _ = _ := by ring

end
end IsingBulk.HT.Final
