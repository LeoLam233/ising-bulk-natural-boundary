import IsingBulk.First.SymmetryIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Field.Lemmas

/-! The physical prefactor branch and the actual infinite source expansion.
Convergence of the physical expansion is explicitly separated from symmetry. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Bornology
open scoped Topology

/-- The fourth-root branch tending to one at infinity. -/
def magnetizationSquared (s : ℂ) : ℂ := (1-(s^(4:ℕ))⁻¹) ^ (1/4:ℂ)

theorem magnetization_argument_slit {s : ℂ} (hs : 1 < ‖s‖) :
    1-(s^(4:ℕ))⁻¹ ∈ Complex.slitPlane := by
  apply Or.inl
  have hn : 1 < ‖s‖^(4:ℕ) := one_lt_pow₀ hs (by decide)
  have hi : ‖(s^(4:ℕ))⁻¹‖ < 1 := by
    rw [norm_inv, norm_pow]
    exact inv_lt_one_of_one_lt₀ hn
  have hre := Complex.re_le_norm ((s^(4:ℕ))⁻¹)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem magnetizationSquared_even (s : ℂ) : magnetizationSquared (-s) = magnetizationSquared s := by
  have he : (-s)^(4:ℕ) = s^(4:ℕ) := by ring
  unfold magnetizationSquared
  rw [he]

theorem magnetizationSquared_conjugate {s : ℂ} (hs : 1 < ‖s‖) :
    magnetizationSquared (star s) = star (magnetizationSquared s) := by
  have ha := Complex.slitPlane_arg_ne_pi (magnetization_argument_slit hs)
  unfold magnetizationSquared
  change (1-((starRingEnd ℂ) s ^ (4:ℕ))⁻¹) ^ (1/4:ℂ) = (starRingEnd ℂ) ((1-(s^(4:ℕ))⁻¹) ^ (1/4:ℂ))
  simpa only [map_sub, map_one, map_inv₀, map_pow, map_div₀, map_ofNat] using Complex.conj_cpow (1-(s^(4:ℕ))⁻¹) (1/4:ℂ) ha

theorem magnetizationSquared_tendsto_one :
    Tendsto magnetizationSquared (cobounded ℂ) (𝓝 1) := by
  have h : Tendsto (fun s : ℂ => 1-(s^(4:ℕ))⁻¹) (cobounded ℂ) (𝓝 1) := by
    have hi := (tendsto_inv₀_cobounded (α := ℂ)).pow 4
    simpa using tendsto_const_nhds.sub hi
  have hc : ContinuousAt (fun z : ℂ => z ^ (1/4:ℂ)) 1 :=
    continuousAt_cpow_const (Or.inl (by norm_num))
  change Tendsto (fun s : ℂ => (1-(s^(4:ℕ))⁻¹) ^ (1/4:ℂ)) (cobounded ℂ) (𝓝 1)
  simpa only [Function.comp_def, Complex.one_cpow] using hc.tendsto.comp h

/-- The literal normalized bulk series in the manuscript, at fixed radius.
Its physical interpretation requires convergence and the physical representation. -/
def normalizedBulkSeries (r : ℝ) (s : ℂ) : ℂ :=
  1-magnetizationSquared s + 2*magnetizationSquared s *
    ∑' n : ℕ, doubleFormFactor (2*(n+1)) r s

theorem normalizedBulkSeries_even (r : ℝ) (s : ℂ) :
    normalizedBulkSeries r (-s) = normalizedBulkSeries r s := by
  unfold normalizedBulkSeries
  rw [magnetizationSquared_even]
  have ht : (∑' n : ℕ, doubleFormFactor (2*(n+1)) r (-s)) =
      ∑' n : ℕ, doubleFormFactor (2*(n+1)) r s := by
    apply tsum_congr
    intro n
    exact doubleFormFactor_even _ (even_two_mul (n+1)) r s
  rw [ht]

theorem normalizedBulkSeries_conjugate (r : ℝ) {s : ℂ} (hs : 1 < ‖s‖) :
    normalizedBulkSeries r (star s) = star (normalizedBulkSeries r s) := by
  have hm := magnetizationSquared_conjugate hs
  have ht : (∑' n : ℕ, doubleFormFactor (2*(n+1)) r (star s)) =
      star (∑' n : ℕ, doubleFormFactor (2*(n+1)) r s) := by
    change _ = (starRingEnd ℂ) _
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    exact doubleFormFactor_conjugate _ r s
  unfold normalizedBulkSeries
  rw [hm, ht]
  simp only [star_add, star_sub, star_one, star_mul, star_ofNat]
  ring

/-- Explicit transfer on the three-point symmetry orbit at a common admissible
radius. There is no assumption that one radius works on the entire exterior.
The only external-facing equalities are the actual physical bulk expansion. -/
theorem susceptibility_symmetry_of_representation (χ : ℂ → ℂ) (r : ℝ) (s : ℂ)
    (hs : 1 < ‖s‖)
    (hphysical : χ s = normalizedBulkSeries r s)
    (hphysical_neg : χ (-s) = normalizedBulkSeries r (-s))
    (hphysical_conj : χ (star s) = normalizedBulkSeries r (star s))
    (_hconvergent : ∀ t ∈ ({s, -s, star s} : Set ℂ),
      Summable (fun n : ℕ => doubleFormFactor (2*(n+1)) r t)) :
    χ (-s) = χ s ∧ χ (star s) = star (χ s) := by
  constructor
  · rw [hphysical_neg, hphysical, normalizedBulkSeries_even]
  · rw [hphysical_conj, hphysical, normalizedBulkSeries_conjugate r hs]

end
end IsingBulk.First
