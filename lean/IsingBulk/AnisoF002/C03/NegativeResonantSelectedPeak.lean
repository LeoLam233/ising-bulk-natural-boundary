import IsingBulk.AnisoF002.C03.NegativeActualSelectedPeak
import IsingBulk.AnisoF002.C03.NegativeCompleteMiddleModel
import IsingBulk.AnisoF002.C03.NegativeTailDominanceScales

/-!
# Arbitrarily late genuine peaks in the full resonant middle window

The selected particle belongs to the exact physical resonance progression.
Its Taylor order is an integer, its neighbors are the actual resonant
neighbors, and its large modulus and full-window membership are proved
simultaneously at any prescribed threshold.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem exists_resonant_selected_model_peak {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : Odd p) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, ∀ K : ℕ, ∃ q j : ℕ,
      K + 1 ≤ q ∧ T ≤ Real.log j ∧ q ∈ resonantMiddleIndices p j ∧
      |actualModelLog B c s (resonantParticleCount p (q + 1)) j -
        actualModelLog B c s (resonantParticleCount p (q - 1)) j| ≤
          (((2 * p : ℕ) : ℝ)) ^ 2 / 4 * Real.log j ∧
      Real.exp (selectedMainExponent D j) ≤
        ‖modelCoefficient (resonantParticleCount p q) j
          (B (windingTau (resonantParticleCount p q) : ℂ))
          (firstWindingCurvature (resonantParticleCount p q)
            (B (windingTau (resonantParticleCount p q) : ℂ)) c s)
          s (windingTau (resonantParticleCount p q))‖ := by
  have hd : Even (2 * p) := even_two_mul p
  have hdpos : 0 < 2 * p := by have := hp.pos; omega
  obtain ⟨D, hD, hselect⟩ := exists_actual_selected_model_peak hB hslit c hs (2 * p) hd hdpos
  refine ⟨D, hD, ?_⟩
  intro T K
  obtain ⟨R, hR, hsel⟩ := hselect (max T 1)
  obtain ⟨l, hl⟩ := exists_nat_gt (max R (Real.exp 256) + (K : ℝ) + 1)
  let n := resonantParticleCount p l
  have hn : Odd n := hp.mul (show Odd (2 * l + 1) from ⟨l, rfl⟩)
  have hlcount : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast index_le_resonantParticleCount hp.pos l
  have hKl : K ≤ l := by
    have hmax0 : 0 ≤ max R (Real.exp 256) := (Real.exp_pos _).le.trans (le_max_right _ _)
    exact_mod_cast (show (K : ℝ) ≤ l by linarith)
  have hRcenter : R ≤ (n : ℝ) + ((2 * p : ℕ) : ℝ) := by
    have hh : R ≤ max R (Real.exp 256) := le_max_left _ _
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hd0 : (0 : ℝ) ≤ (2 * p : ℕ) := Nat.cast_nonneg _
    linarith
  have hExpcenter : Real.exp 256 ≤ (n : ℝ) + ((2 * p : ℕ) : ℝ) := by
    have hh : Real.exp 256 ≤ max R (Real.exp 256) := le_max_right _ _
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hd0 : (0 : ℝ) ≤ (2 * p : ℕ) := Nat.cast_nonneg _
    linarith
  obtain ⟨j, hjT, hlo, hhi, hcross, hnorm⟩ := hsel n hn hRcenter
  have hcenter : n + 2 * p = resonantParticleCount p (l + 1) := by
    dsimp only [n]
    rw [resonantParticleCount_add, Nat.mul_one]
  have hright : n + 2 * (2 * p) = resonantParticleCount p (l + 1 + 1) := by
    dsimp only [n]
    simp only [resonantParticleCount]
    ring
  have hcenter1 : 1 ≤ (n : ℝ) + ((2 * p : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.pos
    have hd0 : (0 : ℝ) ≤ (2 * p : ℕ) := Nat.cast_nonneg _
    linarith
  have hcenter0 : 0 < (n : ℝ) + ((2 * p : ℕ) : ℝ) := by linarith
  have ht : 256 ≤ Real.log ((n : ℝ) + ((2 * p : ℕ) : ℝ)) :=
    (Real.le_log_iff_exp_le hcenter0).mpr hExpcenter
  have hw := selected_scale_middle_window hcenter1 ht hlo hhi
  have hj1 : 1 ≤ Real.log j := (le_max_right _ _).trans hjT
  have hmember : l + 1 ∈ resonantMiddleIndices p j := by
    apply (mem_resonantMiddleIndices_iff hp.pos hj1).mpr
    simpa only [← hcenter, Nat.cast_add] using And.intro hw.1 hw.2.2.1
  refine ⟨l + 1, j, by omega, (le_max_left _ _).trans hjT, hmember, ?_, ?_⟩
  · simpa only [hright, Nat.add_sub_cancel, n] using hcross
  · simpa only [selectedMainExponent, hcenter] using hnorm

end
end IsingBulk.AnisoF002.NegativeHT
