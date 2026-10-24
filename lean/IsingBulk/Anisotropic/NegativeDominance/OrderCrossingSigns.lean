import IsingBulk.Anisotropic.NegativeDominance.CoarseOrderBounds
import IsingBulk.Anisotropic.NegativeDominance.CrossingOrderScale

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem modelLogReal_crossing_signs
    (B R H : ℕ → ℂ) (B0 : ℂ) (s C : ℝ) (n p : ℕ)
    (hn : 2 ≤ n) (hp : 0 < p) (hpn : 2*p ≤ n) (hpi : Real.pi^2 ≤ (n : ℝ))
    (hnodd : Odd n) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hscale : max 64 (2*(2*|modelQuadraticConstant B0 s|+14+2*C)+2) ≤ Real.log (n : ℝ))
    (hupper : 32*Real.log (n : ℝ) ≤ n)
    (hgood : ∀ k ≥ n, Odd k → B k ≠ 0 ∧ R k ≠ 0 ∧ H k ≠ 0 ∧ (R k)^2 = B k)
    (herr : ∀ k ≥ n, Odd k → |modelAnalyticError B0 (B k) (H k) k| ≤ C) :
    (modelLogReal (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) (lowerCrossingOrder n) -
      modelLogReal (B n) (R n) (H n) s n (lowerCrossingOrder n) < 0) ∧
    (0 < modelLogReal (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) (upperCrossingOrder n) -
      modelLogReal (B n) (R n) (H n) s n (upperCrossingOrder n)) := by
  have hl64 : 64 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hscale
  have hlK := (le_max_right _ _).trans hscale
  obtain ⟨hrange, hnL, hLH, hHcube⟩ := crossing_order_range n p hn hpn hnodd hl64 hupper
  have hLalpha : 2*(alpha (n+2*p) : ℝ) ≤ lowerCrossingOrder n := by linarith only [hrange]
  have hHalpha := hLalpha.trans hLH
  have hLo := modelLogReal_coarse_bounds B R H B0 s C n p (lowerCrossingOrder n)
    hn hp hpn hpi hnodd hLalpha hC hs hgood herr
  have hHi := modelLogReal_coarse_bounds B R H B0 s C n p (upperCrossingOrder n)
    hn hp hpn hpi hnodd hHalpha hC hs hgood herr
  dsimp at hLo hHi
  have hlogL := (crossing_order_log_bounds (by omega : 0<n) hnL (hLH.trans hHcube)).1
  have hlogH := (crossing_order_log_bounds (by omega : 0<n) (hnL.trans hLH) hHcube).2
  have hn0 : (0 : ℝ) < n := by positivity
  have hX : 0 < 2*(p : ℝ)*n := by positivity
  have hLex : 3*lowerCrossingOrder n/(n : ℝ)^2 = 3*Real.log (n : ℝ)/16 := by
    dsimp [lowerCrossingOrder]; field_simp
  have hHex : upperCrossingOrder n/(2*(n : ℝ)^2) = 16*Real.log (n : ℝ) := by
    dsimp [upperCrossingOrder]; field_simp; norm_num
  rw [hLex] at hLo
  rw [hHex] at hHi
  have hnLsign : -Real.log (lowerCrossingOrder n)+3*Real.log (n : ℝ)/16+
      (2*|modelQuadraticConstant B0 s|+14+2*C) < 0 := by
    linarith only [hlK, hlogL, hl64]
  have hnHsign : 0 < -2*Real.log (upperCrossingOrder n)+16*Real.log (n : ℝ)-
      (2*|modelQuadraticConstant B0 s|+14+2*C) := by
    linarith only [hlK, hlogH, hl64]
  exact ⟨hLo.2.trans_lt (mul_neg_of_pos_of_neg hX hnLsign),
    (mul_pos hX hnHsign).trans_le hHi.1⟩

end
end IsingBulk.Anisotropic.NegativeDominance
