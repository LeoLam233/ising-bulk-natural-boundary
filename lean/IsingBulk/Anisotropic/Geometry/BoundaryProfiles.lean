import IsingBulk.Anisotropic.Geometry.Profiles

namespace IsingBulk.Anisotropic
noncomputable section

theorem closure_omegaL_subset {lam : ℝ} (hlam : 0 < lam) :
    closure (omegaL lam) ⊆ {z | sliceL lam z.im ≤ z.re} := by
  apply closure_minimal
  · intro z hz
    exact le_of_lt (show sliceL lam z.im < z.re from hz)
  · exact isClosed_le ((sliceL_continuous hlam).comp Complex.continuous_im) Complex.continuous_re

/-- The entire graph, including its axis contacts, is the LT boundary. -/
theorem mem_frontier_omegaL_iff {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    z ∈ frontier (omegaL lam) ↔ z.re = sliceL lam z.im := by
  rw [(omegaL_isOpen hlam).frontier_eq]
  constructor
  · rintro ⟨hz, hn⟩
    have hle := closure_omegaL_subset hlam hz
    change ¬ sliceL lam z.im < z.re at hn
    exact le_antisymm (le_of_not_gt hn) hle
  · intro heq
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closure_iff]
      intro eps heps
      refine ⟨z + ((eps/2 : ℝ) : ℂ), ?_, ?_⟩
      · change sliceL lam (z + ((eps/2 : ℝ) : ℂ)).im < (z + ((eps/2 : ℝ) : ℂ)).re
        simp only [Complex.add_im, Complex.ofReal_im, add_zero,
          Complex.add_re, Complex.ofReal_re, heq]
        linarith
      · have hd : dist z (z + ((eps/2 : ℝ) : ℂ)) = eps/2 := by
          simp [dist_eq_norm]
          exact heps.le
        rw [hd]
        linarith
    · change ¬ sliceL lam z.im < z.re
      rw [heq]
      exact lt_irrefl _

end
end IsingBulk.Anisotropic
