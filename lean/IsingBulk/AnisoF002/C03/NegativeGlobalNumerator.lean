import IsingBulk.AnisoF002.C03.NegativeGlobalPhase

/-!
# Physical square-root normalization in the global matched numerator

The physical root b²=B and the root used for a=-B differ by one constant
unit phase on the common disk.  That phase is retained explicitly in
every finite numerator; no principal-root replacement is made.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem continuous_square_roots_eventually_eq {f g : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (h0 : f 0 = g 0) (hfn : f 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 0, f t ^ 2 = g t ^ 2) : f =ᶠ[𝓝 0] g := by
  have hsum : f 0 + g 0 ≠ 0 := by
    rw [← h0, ← two_mul]
    exact mul_ne_zero (by norm_num) hfn
  filter_upwards [hsq, (hf.add hg).eventually_ne hsum] with t ht hne
  apply sub_eq_zero.mp
  have hh : (f t - g t) * (f t + g t) = 0 := by linear_combination ht
  exact (mul_eq_zero.mp hh).resolve_right hne

theorem physical_root_global_unit_phase {b B : ℂ → ℂ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ ζ : ℂ, ζ ^ 2 = -1 ∧ ‖ζ‖ = 1 ∧
      ∀ᶠ t in 𝓝 0, b t = ζ * edgePrefactor (negativeGlobalCoefficient B) t := by
  let a := negativeGlobalCoefficient B
  let e := edgePrefactor a
  have hB0 : B 0 ≠ 0 := by intro he; simp [he] at hBi
  have hb0 : b 0 ≠ 0 := by
    intro he
    have hs := hbsq 0
    rw [he, zero_pow (by norm_num)] at hs
    exact hB0 hs.symm
  have ha0 : a 0 ≠ 0 := neg_ne_zero.mpr hB0
  have he0 : e 0 ≠ 0 := by
    intro hz
    have hs := edgePrefactor_sq a 0
    change e 0 ^ 2 = a 0 at hs
    rw [hz, zero_pow (by norm_num)] at hs
    exact ha0 hs.symm
  have hslit : a 0 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
    (Or.inr (by change -(B 0).im ≠ 0; exact (neg_pos.mpr hBi).ne'))
  have hea : AnalyticAt ℂ e 0 := edgePrefactor_analyticAt hB.neg hslit
  let ζ := b 0 / e 0
  have hζsq : ζ ^ 2 = -1 := by
    dsimp [ζ]
    rw [div_pow, hbsq 0, edgePrefactor_sq]
    change B 0 / (-B 0) = -1
    field_simp
  have hζnorm : ‖ζ‖ = 1 := by
    have hh := congrArg norm hζsq
    rw [norm_pow, norm_neg, norm_one] at hh
    nlinarith [norm_nonneg ζ]
  refine ⟨ζ, hζsq, hζnorm, ?_⟩
  apply continuous_square_roots_eventually_eq hb.continuousAt (continuousAt_const.mul hea.continuousAt)
  · dsimp [ζ]
    field_simp
  · exact hb0
  · apply Filter.Eventually.of_forall
    intro t
    change b t ^ 2 = (ζ * e t) ^ 2
    rw [mul_pow, hζsq, hbsq t, edgePrefactor_sq]
    dsimp [a, negativeGlobalCoefficient]
    ring

theorem negative_complete_numerator_eq_global_matched (n : ℕ)
    (b B : ℂ → ℂ) (φ : ℝ) (ζ t : ℂ) (x : Fin n → ℝ)
    (hb : b t = ζ * edgePrefactor (negativeGlobalCoefficient B) t) :
    completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (x i : ℂ)) =
      (ζ ^ (n ^ 2) / windingNormalization n) *
        edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t x := by
  rw [edgeFullNumerator_log_normalization]
  unfold completeNegativeNumerator
  simp only [zero_add, negativeGlobalPhase_real, Complex.ofReal_sin, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_ofNat]
  rw [hb, mul_pow]
  ring

theorem eventually_negative_complete_numerator_all_indices {b B : ℂ → ℂ} (φ : ℝ)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ ζ : ℂ, ζ ^ 2 = -1 ∧ ‖ζ‖ = 1 ∧
      ∀ᶠ t in 𝓝 0, ∀ n : ℕ, ∀ x : Fin n → ℝ,
        completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (x i : ℂ)) =
          (ζ ^ (n ^ 2) / windingNormalization n) *
            edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t x := by
  obtain ⟨ζ, hs, hn, he⟩ := physical_root_global_unit_phase hb hB hBi hbsq
  refine ⟨ζ, hs, hn, he.mono ?_⟩
  intro t ht n x
  exact negative_complete_numerator_eq_global_matched n b B φ ζ t x ht

end
end IsingBulk.AnisoF002.NegativeHT
