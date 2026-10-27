import IsingBulk.Preferred22.RadialLogImprovement

/-! The literal finite lower-particle complement, assembled after the
source logarithmic estimates. The next derivative is used before taking
the finite sum, so no value at the boundary is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

theorem preferred_finite_complement_of_next_log_bounds {ζ : ℂ} (hζ : ‖ζ‖=1)
    (m k : ℕ)
    (hlog : ∀ n : ℕ,n<m → ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧
      ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv (k+1) (coefficient (2*(n+1))) ((1+(ε:ℂ))*ζ)‖≤
          C*(1+|Real.log ε|)) :
    PreferredFiniteComplementStatement ζ m k := by
  induction m with
  | zero =>
    refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro ε _ _
    simp
  | succ m ih =>
    obtain ⟨C₀,ε₀,hC₀,hε₀,hrest⟩ := ih (fun n hn => hlog n (by omega))
    obtain ⟨C₁,ε₁,hC₁,hε₁,hterm⟩ := hlog m (by omega)
    have ha : 0<ε₁/2 := by positivity
    obtain ⟨M,hM,hbounded⟩ := preferred_coefficient_log_improvement (2*(m+1)) k hζ
      ha hC₁.le (fun ε hε hεa => hterm ε hε (by linarith))
    refine ⟨C₀+M,min ε₀ (ε₁/2),add_pos hC₀ hM,lt_min hε₀ ha,?_⟩
    intro ε hε hεr
    rw [Finset.sum_range_succ]
    exact add_le_add (hrest ε hε (hεr.trans_le (min_le_left _ _)))
      (hbounded ε hε (hεr.trans_le (min_le_right _ _)).le)

end
end IsingBulk.Preferred22
