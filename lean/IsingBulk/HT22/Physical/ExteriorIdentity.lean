import IsingBulk.HT22.Physical.Holomorphy
import IsingBulk.HT22.Physical.RealIdentification
import IsingBulk.HT.Final.PublishedPhysicalIdentification
import IsingBulk.First.ExteriorIdentitySymmetry

/-!
# Equality of the independently defined F001 coefficients on the entire exterior

Finite-N holomorphy is proved directly for the new signed angular integrals.
Real physical identification and the identity theorem then identify each odd
positive coefficient with the established analytic full-site coefficient.
Only interior compact convergence is transferred. No boundary tail, first
singularity, noncancellation, or old natural-boundary theorem is a premise.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Final Set Filter
open scoped Topology BigOperators

/-- Analytic uniqueness is applied only after proving both holomorphy premises
and the literal real coefficient equality. -/
theorem coefficient_odd_eq_existing_exterior (n : ℕ) :
    EqOn (coefficient (2*n+1)) (exteriorOddTerm n) {t : ℂ | 1 < ‖t‖} := by
  apply exterior_eq_of_real_ray (by norm_num : (0:ℝ) ≤ 1)
    (fun t ht => coefficient_analyticAt _ ht)
    (fun t ht => exteriorOddTerm_analyticAt n ht)
  intro x hx
  obtain ⟨hr, hr1, hm⟩ := realContourRadius_admissible hx
  rw [coefficient_odd_eq_published n hx,
    exteriorOddTerm_eq_right n (physical_real_trace_gt_two hx),
    physicalAngularCoefficient_eq_standardFormFactor (2*n) hx hr hr1 hm,
    rightFullCoefficient_eq_fixed_radius (2*n+1) (by omega) hr hr1 hm]

theorem coefficient_odd_eventuallyEq_existing (n : ℕ) {t : ℂ}
    (ht : 1 < ‖t‖) : coefficient (2*n+1) =ᶠ[𝓝 t] exteriorOddTerm n := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
  exact coefficient_odd_eq_existing_exterior n hz

theorem coefficient_odd_iteratedDeriv_eq_existing (n j : ℕ) {t : ℂ}
    (ht : 1 < ‖t‖) :
    iteratedDeriv j (coefficient (2*n+1)) t = iteratedDeriv j (exteriorOddTerm n) t :=
  (coefficient_odd_eventuallyEq_existing n ht).iteratedDeriv_eq j

/-- Equality is term by term in the full infinite sum, not a finite truncation. -/
theorem oddSeries_eq_existing_exterior {t : ℂ} (ht : 1 < ‖t‖) :
    oddSeries t = exteriorOddSeries t := by
  apply tsum_congr
  intro n
  exact coefficient_odd_eq_existing_exterior n ht

theorem exteriorBulk_eq_existing {t : ℂ} (ht : 1 < ‖t‖) :
    exteriorBulk t = IsingBulk.HT.Final.exteriorFullBulk t := by
  rw [exteriorBulk, oddSeries_eq_existing_exterior ht]
  rfl

/-- The actual new angular sum equals the already constructed physical germ
on the punctured unit disk. No analyticity of the infinite sum is assumed. -/
theorem puncturedInteriorBulk_eq_existing {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1) :
    puncturedInteriorBulk s = interiorFullBulk s := by
  have hi : 1 < ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hs0)).mpr hs
  rw [puncturedInteriorBulk_eq_exterior, exteriorBulk_eq_existing hi,
    interiorFullBulk_eq_exterior hs0]

/-- Compact normal convergence of the positive signed (physical) odd series,
transferred only after the literal finite-coefficient identity has been proved. -/
theorem compact_oddCoefficient_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ {t : ℂ | 1 < ‖t‖}) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ K → ‖coefficient (2*n+1) t‖ ≤ u n := by
  obtain ⟨u, hu, hb⟩ := compact_exteriorOdd_majorant hK hsub
  refine ⟨u, hu, ?_⟩
  intro n t ht
  rw [coefficient_odd_eq_existing_exterior n (hsub ht)]
  exact hb n t ht

/-- Every fixed derivative order has an all-odd-N summable envelope on each
compact subset strictly inside the exterior. -/
theorem compact_oddCoefficient_derivative_majorant {K : Set ℂ} (hK : IsCompact K)
    (hsub : K ⊆ {t : ℂ | 1 < ‖t‖}) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ∈ K →
      ‖iteratedDeriv j (coefficient (2*n+1)) t‖ ≤ u n := by
  obtain ⟨u, hu, hb⟩ := compact_exteriorOdd_derivative_majorant hK hsub j
  refine ⟨u, hu, ?_⟩
  intro n t ht
  rw [coefficient_odd_iteratedDeriv_eq_existing n j (hsub ht)]
  exact hb n t ht

/-- Absolute differentiated convergence at every strictly exterior point;
this is not an estimate uniform as t approaches the unit circle. -/
theorem oddCoefficient_derivative_norm_summable (j : ℕ) {t : ℂ}
    (ht : 1 < ‖t‖) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (coefficient (2*n+1)) t‖) := by
  apply (exteriorOdd_derivative_summable j ht).congr
  intro n
  rw [coefficient_odd_iteratedDeriv_eq_existing n j ht]

theorem oddSeries_analyticAt {t : ℂ} (ht : 1 < ‖t‖) :
    AnalyticAt ℂ oddSeries t := by
  apply (exteriorOddSeries_analyticAt ht).congr
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
  exact (oddSeries_eq_existing_exterior hz).symm

/-- Actual termwise differentiation of the complete new positive odd series. -/
theorem oddSeries_iteratedDeriv (j : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    iteratedDeriv j oddSeries t =
      ∑' n : ℕ, iteratedDeriv j (coefficient (2*n+1)) t := by
  have he : oddSeries =ᶠ[𝓝 t] exteriorOddSeries := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
    exact oddSeries_eq_existing_exterior hz
  rw [he.iteratedDeriv_eq j, exteriorOddSeries_iteratedDeriv j ht]
  apply tsum_congr
  intro n
  exact (coefficient_odd_iteratedDeriv_eq_existing n j ht).symm

end
end IsingBulk.HT22.Physical
