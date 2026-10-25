import IsingBulk.Joint.RegularEdges.PositiveFullSum
import IsingBulk.Anisotropic.RegularEdges.PositiveChartData
import IsingBulk.Anisotropic.RegularEdges.LeadingPrimeCharts
import IsingBulk.Anisotropic.Final.AnalyticFactor

/-! # Physical integer weights on every variable-anisotropy curve
The local square root is constructed from the nonzero particle product. The
complete sums retain their odd versus nonzero-even index sets exactly.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

theorem prime_paritySeries_upperBall {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (hBa : AnalyticAt ℂ B 0) (hBi : 0 < (B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      ¬HasDomainExtension (upperBall r) (paritySeries 0 b B S) 0 ∧
      ¬HasDomainExtension (upperBall r) (paritySeries 1 b B S) 0 := by
  have hev : ∀ᶠ u in 𝓝 (0:ℂ), AnalyticAt ℂ B u ∧ AnalyticAt ℂ S u ∧
      0 < (B u).im ∧ S u ≠ 0 := by
    filter_upwards [hBa.eventually_analyticAt,hSa.eventually_analyticAt,
      (Complex.continuous_im.continuousAt.comp hBa.continuousAt).eventually_const_lt hBi,
      hSa.continuousAt.eventually_ne hS0] with u hbu hsu hbi hs0
    exact ⟨hbu,hsu,hbi,hs0⟩
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ,hδ,?_⟩
  intro r hr hrδ
  have hall (u : ℂ) (hu : u ∈ upperBall r) := hδb (ball_subset_ball hrδ hu.1)
  exact prime_paritySeries_no_extension hb hBi hBa hSa hS0 (upperBall_isOpen r)
    (fun u hu => (hall u hu).1) (fun u hu => (hall u hu).2.1)
    (fun _ hu => hu.2) (fun u hu => (hall u hu).2.2.1)
    (fun u hu => (hall u hu).2.2.2) (upperBall_inward hr) hprime

theorem angularDensity_rescale {N : ℕ} (b : ℝ) (B S R : ℂ → ℂ)
    (u : ℂ) (q : Fin N → ℝ) :
    edgeAngularDensity b B (fun v => S v / R v) u q =
      (R u)^N * edgeAngularDensity b B S u q := by
  simp only [edgeAngularDensity,edgeAngularWeight,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  ring

/-- Exact all-particle normalization: the factor has exponent `n+1`, not `n`. -/
theorem angularCoefficient_rescale (n : ℕ) (b : ℝ) (B S R : ℂ → ℂ) (u : ℂ) :
    angularCoefficient n b B (fun v => S v / R v) u =
      (R u)^(n+1) * angularCoefficient n b B S u := by
  simp only [angularCoefficient,angularDensity_rescale,integral_const_mul]
  ring

def weightedOddSeries (b : ℝ) (B S P : ℂ → ℂ) (u : ℂ) : ℂ :=
  ∑' i, (P u)^i * angularCoefficient (2*i) b B S u

def weightedEvenSeries (b : ℝ) (B S P : ℂ → ℂ) (u : ℂ) : ℂ :=
  ∑' i, (P u)^(i+1) * angularCoefficient (2*i+1) b B S u

theorem oddSeries_rescale (b : ℝ) (B S R P : ℂ → ℂ) (u : ℂ)
    (hR : (R u)^2 = P u) :
    paritySeries 0 b B (fun v => S v / R v) u = R u * weightedOddSeries b B S P u := by
  unfold paritySeries weightedOddSeries
  simp only [Nat.add_zero,angularCoefficient_rescale]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro i
  rw [pow_add,pow_mul,hR,pow_one]
  ring

theorem evenSeries_rescale (b : ℝ) (B S R P : ℂ → ℂ) (u : ℂ)
    (hR : (R u)^2 = P u) :
    paritySeries 1 b B (fun v => S v / R v) u = weightedEvenSeries b B S P u := by
  unfold paritySeries weightedEvenSeries
  simp only [angularCoefficient_rescale]
  apply tsum_congr
  intro i
  rw [show 2*i+1+1=2*(i+1) by omega,pow_mul,hR]

/-- The physical integer-weighted complete sums inherit the all-curve
obstructions. The needed square root is internally constructed. -/
theorem weighted_prime_upperBall_no_extension {b : ℝ} {B S P : ℂ → ℂ}
    (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (hBa : AnalyticAt ℂ B 0) (hBi : 0 < (B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0)
    (hPa : AnalyticAt ℂ P 0) (hP0 : P 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      ¬HasDomainExtension (upperBall r) (weightedOddSeries b B S P) 0 ∧
      ¬HasDomainExtension (upperBall r) (weightedEvenSeries b B S P) 0 := by
  let R := localParticleRoot P
  have hRa : AnalyticAt ℂ R 0 := localParticleRoot_analyticAt hPa hP0
  have hR0 : R 0 ≠ 0 := localParticleRoot_ne_zero hP0
  have hR (u : ℂ) : R u ^ 2 = P u := localParticleRoot_sq hP0 u
  obtain ⟨δ,hδ,hno⟩ := prime_paritySeries_upperBall hb hprime hBa hBi
    (hSa.div hRa hR0) (div_ne_zero hS0 hR0)
  refine ⟨δ,hδ,?_⟩
  intro r hr hrδ
  constructor
  · intro hext
    apply (hno r hr hrδ).1
    apply domain_extension_of_eqOn (g := fun u => R u * weightedOddSeries b B S P u)
      (fun u _ => oddSeries_rescale b B S R P u (hR u))
    exact domain_extension_mul_analyticAt hRa hext
  · exact no_domain_extension_of_eqOn
      (fun u _ => evenSeries_rescale b B S R P u (hR u)) (hno r hr hrδ).2

/-- A nonzero analytic physical prefactor cannot remove either full obstruction. -/
theorem normalized_prime_upperBall_no_extension {b : ℝ} {B S P H L : ℂ → ℂ}
    (hb : |b| < 1) (hprime : b ∈ primePhaseCosines)
    (hBa : AnalyticAt ℂ B 0) (hBi : 0 < (B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0 ≠ 0)
    (hPa : AnalyticAt ℂ P 0) (hP0 : P 0 ≠ 0)
    (hHa : AnalyticAt ℂ H 0) (hH0 : H 0 ≠ 0)
    (hLa : AnalyticAt ℂ L 0) (hL0 : L 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      ¬HasDomainExtension (upperBall r) (fun u => H u * weightedOddSeries b B S P u) 0 ∧
      ¬HasDomainExtension (upperBall r) (fun u => L u * weightedEvenSeries b B S P u) 0 := by
  obtain ⟨δ,hδ,hno⟩ := weighted_prime_upperBall_no_extension hb hprime hBa hBi hSa hS0 hPa hP0
  refine ⟨δ,hδ,fun r hr hrδ => ⟨?_,?_⟩⟩
  · exact fun he => (hno r hr hrδ).1 (domain_extension_of_analytic_factor hHa hH0 he)
  · exact fun he => (hno r hr hrδ).2 (domain_extension_of_analytic_factor hLa hL0 he)

end
end IsingBulk.Joint.RegularEdges
