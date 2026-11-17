import IsingBulk.AnisoF002.C03.NegativeSelectedWindowGates

/-!
# A genuine integer-selected physical-model peak with uniform growth

The growth constant is chosen before an arbitrary requested logarithmic
Taylor-order threshold.  The selected order simultaneously has the exact
particle scale, the adjacent gap needed for every competitor sum, and the
large modulus of the original complete complex first-winding model.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem exists_actual_selected_model_peak {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, ∃ R : ℝ, 0 < R ∧
      ∀ n : ℕ, Odd n → R ≤ (n : ℝ) + d → ∃ j : ℕ,
        T ≤ Real.log j ∧
        ((n : ℝ) + d) ^ 2 * Real.log ((n : ℝ) + d) / 3 ≤ (j : ℝ) ∧
        (j : ℝ) ≤ 3 * ((n : ℝ) + d) ^ 2 * Real.log ((n : ℝ) + d) / 2 ∧
        |actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j| ≤
          (d : ℝ) ^ 2 / 4 * Real.log j ∧
        Real.exp ((j : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.log j) - D * j) ≤
          ‖modelCoefficient (n + d) j (B (windingTau (n + d) : ℂ))
            (firstWindingCurvature (n + d) (B (windingTau (n + d) : ℂ)) c s)
            s (windingTau (n + d))‖ := by
  obtain ⟨D, Rg, hD, hRg, hgrowth⟩ := exists_actual_selected_model_growth hB hslit c hs
  obtain ⟨K, Rs, hK, hRs, hselect⟩ := exists_actual_model_integer_crossing hB hslit c hs d hd hdpos
  refine ⟨D, hD, ?_⟩
  intro T
  let U : ℝ := max 256 T
  let R : ℝ := max Rg (max Rs (max (K + 1) (Real.exp U)))
  refine ⟨R, hRg.trans_le (le_max_left _ _), ?_⟩
  intro n hn hlarge
  have hRgN : Rg ≤ (n : ℝ) + d := (le_max_left _ _).trans hlarge
  have hRsN : Rs ≤ (n : ℝ) + d :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hKN : K + 1 ≤ (n : ℝ) + d :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hExp : Real.exp U ≤ (n : ℝ) + d :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hN0 : 0 < (n : ℝ) + d := hRg.trans_le hRgN
  have hN1 : 1 ≤ (n : ℝ) + d := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.pos
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hU : U ≤ Real.log ((n : ℝ) + d) := (Real.le_log_iff_exp_le hN0).mpr hExp
  have ht : 256 ≤ Real.log ((n : ℝ) + d) := (le_max_left _ _).trans hU
  have hT : T ≤ Real.log ((n : ℝ) + d) := (le_max_right _ _).trans hU
  obtain ⟨j, _, _, hF0, hF, hlo, hhi⟩ := hselect n hn hRsN
  obtain ⟨hloglo, _⟩ := selected_scale_log_range hN1 ht hlo hhi
  have hjT : T ≤ Real.log j := by linarith
  have hj4 : 4 ≤ Real.log j := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hd2 : 1 ≤ (d : ℝ) ^ 2 := by nlinarith
  have hgapscale : 1 ≤ (d : ℝ) ^ 2 / 4 * Real.log j := by
    have hh := mul_le_mul_of_nonneg_left hj4 (sq_nonneg (d : ℝ))
    nlinarith
  have hratio : K / ((n : ℝ) + d) ≤ 1 := (div_le_one hN0).mpr (by linarith)
  have hcross : |actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j| ≤
      (d : ℝ) ^ 2 / 4 * Real.log j := by
    change |actualModelCrossing B c s n d j| ≤ _
    rw [abs_of_nonneg hF0]
    exact hF.trans (hratio.trans hgapscale)
  have hNgrowth := hgrowth (n + d) j (hn.add_even hd)
    (by simpa only [Nat.cast_add] using hRgN)
    (by simpa only [Nat.cast_add] using hlo)
    (by simpa only [Nat.cast_add] using hhi)
  exact ⟨j, hjT, hlo, hhi, hcross, hNgrowth.2⟩

end
end IsingBulk.AnisoF002.NegativeHT
