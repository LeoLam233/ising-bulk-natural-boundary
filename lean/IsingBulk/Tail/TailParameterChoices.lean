import Mathlib.Tactic

/-! Finite fixed-derivative threshold consolidation. This does not choose
independent selectors: geometric eta/alpha/tau choices must already agree. -/
namespace IsingBulk.Tail
noncomputable section

theorem common_finite_derivative_threshold (k : ℕ) (P : ℕ → ℝ → Prop)
    (h : ∀ j : ℕ, j ≤ k → ∃ e : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps < e → P j eps) :
    ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j ≤ k → ∀ eps : ℝ, 0 < eps → eps < e → P j eps := by
  induction k with
  | zero =>
    obtain ⟨e,he,hp⟩ := h 0 (by omega)
    refine ⟨e,he,?_⟩
    intro j hj eps hp0 hpe
    have hj0 : j=0 := by omega
    exact hj0 ▸ hp eps hp0 hpe
  | succ k ih =>
    obtain ⟨e0,he0,hp0⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨e1,he1,hp1⟩ := h (k+1) (by omega)
    refine ⟨min e0 e1,lt_min he0 he1,?_⟩
    intro j hj eps heps hsmall
    by_cases hjk : j ≤ k
    · exact hp0 j hjk eps heps (hsmall.trans_le (min_le_left _ _))
    · have heq : j=k+1 := by omega
      exact heq ▸ hp1 eps heps (hsmall.trans_le (min_le_right _ _))

end
end IsingBulk.Tail
