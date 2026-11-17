import IsingBulk.AnisoF002.C03.NegativeCoefficientControl

/-!
# Actual spectral attachment of the global negative-edge coefficient phase

The local temperature inverse and B=T/S are constructed from the literal
spectral functions.  The global phase then gives the unique canonical
small root at every real angle on one inward interval, before N.  This
joins the complete coefficient disks to the physical branch on the
entire real cycle, not only near a collision center.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open scoped Topology BigOperators

theorem exists_negative_global_physical_chart {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hside : (spectralT lam z / spectralS z).im < 0) :
    ∃ Z B : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ᶠ t in 𝓝 0, negativeParameterF002 lam (Real.cos φ) (Z t) = t) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeParameterF002 lam (Real.cos φ) w) = w) ∧
      ∃ d : NegativeCoefficientControl B φ,
        ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ d.eps0 ∧
          ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
            spectralS (Z (-(eps : ℂ))) ≠ 0 ∧
            ∀ q : ℝ,
              0 < (negativeGlobalPhase B φ (-(eps : ℂ), ((q - Real.pi : ℝ) : ℂ))).re ∧
              Complex.exp (-negativeGlobalPhase B φ (-(eps : ℂ), ((q - Real.pi : ℝ) : ℂ))) =
                spectralSmallRootF002 lam (Z (-(eps : ℂ))) q := by
  have hsin : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)
  obtain ⟨Z, B, hZa, hZ0, hBa, hB0, hBne, hBe, hp, hleft⟩ :=
    exists_negative_physical_chart hlam hx (abs_cos_lt_one_of_sin_ne_zero hsin) hinc
  have hBi : (B 0).im < 0 := by rwa [hB0]
  obtain ⟨d⟩ := exists_negative_coefficient_control hBa hφ0 hφpi hBi
  obtain ⟨r, hr, hpr⟩ := Metric.eventually_nhds_iff.mp hp
  let eps0 : ℝ := min (r / 2) d.eps0
  have heps0 : 0 < eps0 := lt_min (half_pos hr) d.eps0_pos
  refine ⟨Z, B, hZa, hZ0, hBa, hB0, hBne, hBe, hp.mono (fun _ h => h.1),
    hleft, d, eps0, heps0, min_le_right _ _, ?_⟩
  intro eps he he0
  have heD : eps ≤ d.eps0 := he0.trans (min_le_right _ _)
  have ht : dist (-(eps : ℂ)) 0 < r := by
    rw [dist_zero_right, norm_neg, Complex.norm_real, Real.norm_of_nonneg he.le]
    exact (he0.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hp' := hpr ht
  refine ⟨hp'.2.1, ?_⟩
  intro q
  have hgpos : 0 < (negativeGlobalPhase B φ (-(eps : ℂ), ((q - Real.pi : ℝ) : ℂ))).re := by
    have hbound := d.cosine_lower eps he.le heD (q - Real.pi)
    have hpositive : 0 < eps + 1 - Real.cos (q - Real.pi) := by
      linarith [Real.cos_le_one (q - Real.pi)]
    exact (mul_pos d.attenuation_pos hpositive).trans_le hbound
  refine ⟨hgpos, phase_exp_eq_spectralSmallRoot hp'.2.1 ?_ hgpos⟩
  have hspec := hp'.2.2.2 (((q - Real.pi : ℝ) : ℂ))
  have hangle : (Real.pi : ℂ) + ((q - Real.pi : ℝ) : ℂ) = (q : ℂ) := by
    push_cast
    ring
  rw [hangle, ← Complex.ofReal_cos] at hspec
  rw [negativeGlobalPhase_cosh]
  calc
    localNegativeDispersion B φ (-(eps : ℂ), ((q - Real.pi : ℝ) : ℂ)) =
        (Real.cos φ : ℂ) + B (-(eps : ℂ)) *
          (-(eps : ℂ) - 1 + Complex.cos ((q - Real.pi : ℝ) : ℂ)) := by
      unfold localNegativeDispersion
      ring
    _ = _ := hspec.symm

end
end IsingBulk.AnisoF002.NegativeHT
