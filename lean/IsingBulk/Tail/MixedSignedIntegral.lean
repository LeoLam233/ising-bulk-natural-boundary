import IsingBulk.Tail.MixedNegativeSupportedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory

/-- Sign division takes place only after absolute values, so overlapping
zero-angle boundaries require no differentiation of a sign cutoff. -/
theorem mixed_integral_norm_le_signed_halves {N : ℕ} (b : ℝ) (j : Fin N)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F (angleBox N)) :
    (∫ θ in angleBox N,‖F θ‖)≤
      (∫ θ in mixedPositiveAngularHalf b j,‖F θ‖)+
        (∫ θ in mixedNegativeAngularHalf b j,‖F θ‖) := by
  have hpos : mixedPositiveAngularHalf b j⊆angleBox N := fun _ hθ => hθ.1
  have hneg : mixedNegativeAngularHalf b j⊆angleBox N := fun _ hθ => hθ.1
  have hsub : angleBox N\mixedPositiveAngularHalf b j⊆mixedNegativeAngularHalf b j := by
    intro θ hθ
    refine ⟨hθ.1,?_⟩
    have hh : ¬0≤θ j+b-2*Real.pi := fun hp => hθ.2 ⟨hθ.1,hp⟩
    exact (lt_of_not_ge hh).le
  have he := setIntegral_sdiff (mixedPositiveAngularHalf_measurable b j) hF.norm hpos
  have hh := setIntegral_mono_set (hF.mono_set hneg).norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (Filter.Eventually.of_forall hsub)
  rw [he] at hh
  linarith

theorem mixed_norm_integral_le_signed_halves {N : ℕ} (b : ℝ) (j : Fin N)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F (angleBox N)) {P M : ℝ}
    (hP : (∫ θ in mixedPositiveAngularHalf b j,‖F θ‖)≤P)
    (hM : (∫ θ in mixedNegativeAngularHalf b j,‖F θ‖)≤M) :
    ‖∫ θ in angleBox N,F θ‖≤P+M :=
  (norm_integral_le_integral_norm _).trans ((mixed_integral_norm_le_signed_halves b j F hF).trans (add_le_add hP hM))

end
end IsingBulk.Tail
