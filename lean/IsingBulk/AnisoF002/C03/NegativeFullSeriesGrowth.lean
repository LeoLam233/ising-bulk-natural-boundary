import IsingBulk.AnisoF002.C03.NegativeWholeSeriesAssembly
import IsingBulk.AnisoF002.C03.NegativeResonantSelectedPeak

/-!
# Full-series growth from the actual model and complete range bounds

The selected peak, all middle competitors, the whole outside-middle
infinite tail and the analytic remainder use one Taylor order. Every
geometric coefficient bound is contradicted. This assembly theorem has
explicit quantitative inputs; its physical instantiation is separate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

def resonantFullModelCoefficient (B : ℂ → ℂ) (c s : ℝ) (p j q : ℕ) : ℂ :=
  modelCoefficient (resonantParticleCount p q) j
    (B (windingTau (resonantParticleCount p q) : ℂ))
    (firstWindingCurvature (resonantParticleCount p q)
      (B (windingTau (resonantParticleCount p q) : ℂ)) c s)
    s (windingTau (resonantParticleCount p q))

theorem full_residue_taylor_growth_from_complete_bounds {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : Odd p)
    (P : ℕ → ℕ → ℂ) (rem : ℕ → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (A : ℝ)
    (hP : ∀ j : ℕ, Summable fun q => ‖P j q‖)
    (hrem : ∀ j : ℕ, ‖rem j‖ ≤ Real.exp (completeAnalyticExponent A j))
    (heventually : ∀ᶠ j : ℕ in atTop,
      (∀ q ∈ resonantMiddleIndices p j,
        ‖P j q - ζ * resonantFullModelCoefficient B c s p j q‖ ≤
          ‖resonantFullModelCoefficient B c s p j q‖ / 16) ∧
      (∑' q : ℕ, ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ) else P j q‖) ≤
        Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) +
          Real.exp (completeHighExponent A j)) :
    ∀ M R : ℝ, 0 < M → 0 < R → ∃ j : ℕ,
      M / R ^ j < ‖(∑' q : ℕ, P j q) + rem j‖ := by
  obtain ⟨D, hD, hpeak⟩ := exists_resonant_selected_model_peak hB hslit c hs hp
  obtain ⟨Tc, _, hcomp⟩ := exists_complete_middle_model_competitor_bound hB hslit c hs hp
  obtain ⟨J, hJ⟩ := eventually_atTop.mp heventually
  intro M R hM hR
  obtain ⟨Tt, _, htail⟩ := exists_complete_tail_domination_threshold (A := A) hD.le hM hR
  let T : ℝ := max 1 (max (J : ℝ) (max Tc (max Tt (8 * Real.log 64))))
  obtain ⟨q, j, hq1, hjT, hq, hcross, hmain⟩ := hpeak T 0
  have hj1 : 1 ≤ Real.log j := (le_max_left _ _).trans hjT
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    norm_num [hz] at hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hJlog : (J : ℝ) ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hjT)
  have hjJ : J ≤ j := by
    have hh := Real.log_le_sub_one_of_pos hj0
    exact_mod_cast (show (J : ℝ) ≤ j by linarith)
  have hjc : Tc ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hjT))
  have hjt : Tt ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hjT)))
  have hjg : 8 * Real.log 64 ≤ Real.log j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hjT)))
  have hd1 : (1 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
    have hpp := hp.pos
    exact_mod_cast (show 1 ≤ 2 * p by omega)
  have hfactor := (modelCompetitorFactor_small hd1 hjg).2
  have hc := hcomp j q (by omega) hjc hq hcross
  have hcompetitors :
      (∑ k ∈ (resonantMiddleIndices p j).erase q,
        ‖resonantFullModelCoefficient B c s p j k‖) ≤
          ‖resonantFullModelCoefficient B c s p j q‖ / 16 := by
    apply hc.trans
    have hh := mul_le_mul_of_nonneg_left hfactor
      (norm_nonneg (resonantFullModelCoefficient B c s p j q))
    simpa only [modelCompetitorFactor, resonantFullModelCoefficient, div_eq_mul_inv, one_mul] using hh
  obtain ⟨herror, houtside⟩ := hJ j hjJ
  obtain ⟨hl, ha, hh, hgeometric⟩ := htail j hjt
  have hout :
      (∑' k : ℕ, ‖if k ∈ resonantMiddleIndices p j then (0 : ℂ) else P j k‖) ≤
        3 * Real.exp (selectedMainExponent D j) / 64 := by linarith
  have hbound := complete_residue_series_half_lower_bound (P j)
    (resonantFullModelCoefficient B c s p j) (resonantMiddleIndices p j) q hq ζ (rem j)
    (Real.exp (selectedMainExponent D j)) (hP j) hζ hmain hcompetitors herror hout
    ((hrem j).trans ha)
  exact ⟨j, hgeometric.trans_le hbound⟩

end
end IsingBulk.AnisoF002.NegativeHT
