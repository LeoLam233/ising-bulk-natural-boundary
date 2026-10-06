import IsingBulk.First.NearInfinityBulkSeries
import IsingBulk.First.FarExteriorRadiusIndependence

/-! The physical representation input is confined to real low temperatures.
It identifies the normalized response, not the response multiplied by inverse
temperature. No complex full-series convergence or symmetry is imported. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- E1: the normalized real low-temperature representation from the published
Tracy--Widom Appendix 1, equations (7)--(8), and the manuscript's normalized
offsite convention in section 2 and Appendix F. This is a theorem parameter. -/
def RealNormalizedFredholmRepresentation (X : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧
    ∀ r : ℝ, r₀ < r → r < 1 →
      Summable (fun n : ℕ => doubleFormFactor (2*(n+1)) r (x:ℂ)) ∧
      X (x:ℂ)=normalizedBulkSeries r (x:ℂ)

theorem normalizedBulkSeries_radius_eq_farExterior {r : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hr1 : r < 1) {s : ℂ} (hs : 16 < ‖s‖) :
    normalizedBulkSeries r s=normalizedBulkSeries (1/4) s := by
  have he : (∑' n : ℕ, doubleFormFactor (2*(n+1)) r s) =
      ∑' n : ℕ, doubleFormFactor (2*(n+1)) (1/4) s := by
    apply tsum_congr
    intro n
    exact farExterior_doubleFormFactor_radius_eq _ (by omega) le_rfl hr1 hr hs
  simp only [normalizedBulkSeries, he]

/-- Actual annulus moves identify the real physical expansion with the
constructed normally convergent small-radius germ. -/
theorem realNormalizedFredholmRepresentation_quarter (X : ℂ → ℂ)
    (hphysical : RealNormalizedFredholmRepresentation X) (x : ℝ) (hx : 16 < x) :
    X (x:ℂ)=normalizedBulkSeries (1/4) (x:ℂ) := by
  obtain ⟨r₀, _hr₀, hr₀1, hrep⟩ := hphysical x (by linarith)
  let r : ℝ := (max r₀ (1/4)+1)/2
  have hm : max r₀ (1/4:ℝ) < 1 := max_lt hr₀1 (by norm_num)
  have hr₀r : r₀ < r := by dsimp only [r]; have h := le_max_left r₀ (1/4:ℝ); linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hr : (1/4:ℝ) ≤ r := by dsimp only [r]; have h := le_max_right r₀ (1/4:ℝ); linarith
  have hcx : 16 < ‖(x:ℂ)‖ := by simpa [Complex.norm_real, abs_of_pos (show 0 < x by linarith)] using hx
  exact (hrep r hr₀r hr1).2.trans (normalizedBulkSeries_radius_eq_farExterior hr hr1 hcx)

end
end IsingBulk.First
