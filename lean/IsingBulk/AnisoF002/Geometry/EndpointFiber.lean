import IsingBulk.AnisoF002.Geometry.EndpointBridge

/-!
# A singular real-linear fiber reaches the boundary of the cosine square

This is the degenerate-fiber step in F002 Lemma 2.1.  It is an explicit
construction on the actual closed square, with no rank-genericity assumption.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section

theorem real_square_fiber_endpoint_nonneg (k u v : ℝ) (hk : 0 ≤ k)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ a b : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 ∧ b ∈ Set.Icc (-1 : ℝ) 1 ∧
      ((a = 1 ∨ a = -1) ∨ (b = 1 ∨ b = -1)) ∧ a + k * b = u + k * v := by
  have hlo : -1 - k ≤ u + k * v := by nlinarith [hu.1, hv.1]
  have hhi : u + k * v ≤ 1 + k := by nlinarith [hu.2, hv.2]
  by_cases hc : u + k * v ≤ 1 - k
  · refine ⟨u + k * v + k, -1, ⟨by linarith, by linarith⟩, ?_,
      Or.inr (Or.inr rfl), ?_⟩
    · norm_num
    · ring
  · have hkpos : 0 < k := by
      by_contra hn
      have hz : k = 0 := le_antisymm (le_of_not_gt hn) hk
      subst k
      simp only [zero_mul, add_zero, sub_zero] at hc
      exact hc hu.2
    refine ⟨1, (u + k * v - 1) / k, ?_, ⟨?_, ?_⟩,
      Or.inl (Or.inl rfl), ?_⟩
    · norm_num
    · apply (le_div_iff₀ hkpos).2
      linarith
    · apply (div_le_iff₀ hkpos).2
      linarith
    · field_simp
      ring

theorem real_square_fiber_endpoint (k u v : ℝ)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ a b : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 ∧ b ∈ Set.Icc (-1 : ℝ) 1 ∧
      ((a = 1 ∨ a = -1) ∨ (b = 1 ∨ b = -1)) ∧ a + k * b = u + k * v := by
  by_cases hk : 0 ≤ k
  · exact real_square_fiber_endpoint_nonneg k u v hk hu hv
  · have hv' : -v ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    obtain ⟨a, b, ha, hb, hend, hval⟩ :=
      real_square_fiber_endpoint_nonneg (-k) u (-v) (by linarith) hu hv'
    refine ⟨a, -b, ha, ⟨by linarith [hb.2], by linarith [hb.1]⟩, ?_, ?_⟩
    · rcases hend with haend | hbend
      · exact Or.inl haend
      · rcases hbend with rfl | rfl <;> norm_num
    · convert hval using 1 <;> ring

/-- For a singular pair of complex spectral directions, every nonempty fiber
through the closed real cosine square also has an endpoint representation. -/
theorem complex_singular_square_fiber_endpoint (S T : ℂ) (u v : ℝ)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (hv : v ∈ Set.Icc (-1 : ℝ) 1)
    (hdet : S.re * T.im - S.im * T.re = 0) :
    ∃ a b : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 ∧ b ∈ Set.Icc (-1 : ℝ) 1 ∧
      ((a = 1 ∨ a = -1) ∨ (b = 1 ∨ b = -1)) ∧
      S * (a : ℂ) + T * (b : ℂ) = S * (u : ℂ) + T * (v : ℂ) := by
  by_cases hS : S = 0
  · refine ⟨1, v, by norm_num, hv, Or.inl (Or.inl rfl), ?_⟩
    simp only [hS, zero_mul, zero_add]
  · let k : ℝ := (T / S).re
    have hi : (T / S).im = 0 := by
      have hnum : T.im * S.re - T.re * S.im = 0 := by nlinarith [hdet]
      rw [Complex.div_im, ← sub_div, hnum, zero_div]
    have hk : T = S * (k : ℂ) := by
      have hk' : (k : ℂ) = T / S := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hi.symm
      rw [hk']
      field_simp
    obtain ⟨a, b, ha, hb, hend, hval⟩ := real_square_fiber_endpoint k u v hu hv
    refine ⟨a, b, ha, hb, hend, ?_⟩
    have hvalC : (a : ℂ) + (k : ℂ) * (b : ℂ) =
        (u : ℂ) + (k : ℂ) * (v : ℂ) := by exact_mod_cast hval
    rw [hk]
    calc
      _ = S * ((a : ℂ) + (k : ℂ) * (b : ℂ)) := by ring
      _ = S * ((u : ℂ) + (k : ℂ) * (v : ℂ)) := by rw [hvalC]
      _ = _ := by ring

end
end IsingBulk.AnisoF002.Geometry
