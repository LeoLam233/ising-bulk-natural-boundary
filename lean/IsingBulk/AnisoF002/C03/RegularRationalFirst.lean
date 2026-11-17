import IsingBulk.AnisoF002.C03.RegularFirstSeriesLimit

/-!
# Actual odd and even full-series first limits at rational regular edges

The first odd resonance is p and the first even resonance is 2p for
every reduced rational phase with odd denominator p.  No coefficient
is omitted from either series, and the complete tail is differentiated.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Filter Set
open scoped Topology

theorem regularRational_cos_abs_lt_one {r p : ℕ} (hr : 0 < r) (hrp : 2 * r < p) :
    |Real.cos (regularRationalAngle r p)| < 1 := by
  have hφ := regularRationalAngle_mem hr hrp
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have hs := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
  nlinarith [Real.sin_sq_add_cos_sq (regularRationalAngle r p)]

namespace RegularEdgeCompleteControl

/-- First singular derivative of the entire odd particle series, at its
actual first resonant particle number p. -/
theorem rational_odd_series_first_limit {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ 2 * iteratedDeriv (oddTopOrder p)
      (edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 0)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude (Real.cos (regularRationalAngle r p)) a
        (p - 1) (oddTopOrder p))) := by
  have hp0 : 0 < p := by omega
  have hi : 0 + 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  have hi1 : 0 + 2 * ((p - 1) / 2) + 1 = p := by omega
  have hodd : Odd (0 + 2 * ((p - 1) / 2) + 1) := by rw [hi1]; exact hp
  have hres : upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ) ^
      (0 + 2 * ((p - 1) / 2) + 1) = 1 := by
    rw [hi1]
    exact (upperEdgeRoot_rational_resonance_iff hr hrp hcop p).mpr (dvd_refl p)
  have hlower (t : ℕ) (ht : t < (p - 1) / 2) :
      upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ) ^ (0 + 2 * t + 1) ≠ 1 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      ((upperEdgeRoot_rational_resonance_iff hr hrp hcop (0 + 2 * t + 1)).mp he)
  have h := d.particleSeries_first_limit (by norm_num : 0 < 2)
    (odd_first_scaling_degree hodd) (odd_derivative_budget (le_refl _))
    (regularRational_cos_abs_lt_one hr hrp) ha hres hlower
  simpa only [hi, Nat.sub_add_cancel hp0] using h

/-- First singular derivative of the entire even particle series, at
its actual first resonant particle number 2p. -/
theorem rational_even_series_first_limit {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    Tendsto (fun s : ℝ => (s : ℂ) * iteratedDeriv (evenTopOrder (2 * p))
      (edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 1)
        (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (regularFirstAmplitude (Real.cos (regularRationalAngle r p)) a
        (2 * p - 1) (evenTopOrder (2 * p)))) := by
  have hp0 : 0 < p := by omega
  have hi : 1 + 2 * (p - 1) = 2 * p - 1 := by omega
  have hi1 : 1 + 2 * (p - 1) + 1 = 2 * p := by omega
  have heven : Even (1 + 2 * (p - 1) + 1) := ⟨p, by omega⟩
  have hres : upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ) ^
      (1 + 2 * (p - 1) + 1) = 1 := by
    rw [hi1]
    exact (upperEdgeRoot_rational_resonance_iff hr hrp hcop (2 * p)).mpr ⟨2, by omega⟩
  have hlower (t : ℕ) (ht : t < p - 1) :
      upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ) ^ (1 + 2 * t + 1) ≠ 1 := by
    intro he
    exact odd_denominator_even_nonresonance hp (by omega) ⟨t + 1, by omega⟩ (by omega)
      ((upperEdgeRoot_rational_resonance_iff hr hrp hcop (1 + 2 * t + 1)).mp he)
  have h := d.particleSeries_first_limit (by norm_num : 0 < 1)
    (even_first_scaling_degree heven) (even_derivative_budget (le_refl _))
    (regularRational_cos_abs_lt_one hr hrp) ha hres hlower
  simpa only [hi, Nat.sub_add_cancel (show 1 ≤ 2 * p by omega), pow_one] using h

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
