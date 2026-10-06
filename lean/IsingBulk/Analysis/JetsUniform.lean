import IsingBulk.Analysis.JetsChildBounds

/-! Uniform estimates for the same recursively generated semantic term list.
The only neighborhoods used to choose constants have dimension two or three. -/
namespace IsingBulk.Jets
noncomputable section

theorem generated_regularPart_bound {N : ℕ} (p q : Fin N) (j r : ℕ)
    (z : ℂ × (Fin N → ℂ)) (C : ℝ) (hN : 1 ≤ N)
    (h : ScalarBounds p q z (j+r+1) C) (T : SourceJetTerm N)
    (hT : T ∈ sourceJetTerms p q j) :
    JetBound T.regularPart z r
      ((stepScale (j+r) (2*j) (fieldBoundConstant (j+r) C))^j*N^(4*j)) := by
  obtain ⟨hB,hδ,hV,hR,hD⟩ := h.all_fields hN
  let B := fieldBoundConstant (j+r) C
  have hB₀ : 0 ≤ B := (by norm_num : (0:ℝ) ≤ 2).trans hB
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hF : 2 ≤ B*N^2 := hB.trans
    (le_mul_of_one_le_right hB₀ (one_le_pow₀ hn))
  have hb := sourceJetTerms_budget_bound p q j r z (B*N^2) hF hδ hV hR hD j le_rfl T hT
  simp only [Nat.add_sub_cancel_left] at hb
  apply hb.mono le_rfl
  have hstep := stepScale_dimension (j+r) (2*j) hB₀ N hN
  calc
    _ ≤ (stepScale (j+r) (2*j) B*N^4)^j := pow_le_pow_left₀
      (zero_le_one.trans (stepScale_one_le _ _ (by positivity))) hstep j
    _ = _ := by rw [mul_pow,← pow_mul]

/-- The fixed recurrence order and output jet order precede the neighborhoods,
the source constant, every dimension, and every distinct selected pair. -/
theorem sourceJetTerms_uniform (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (j r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∃ U : Set (ℂ × ℂ), ∃ P : Set (ℂ × ℂ × ℂ),
      IsOpen U ∧ (s,0) ∈ U ∧ IsOpen P ∧ (s,0,0) ∈ P ∧
      ∀ N : ℕ, 1 ≤ N → ∀ p q : Fin N, p ≠ q →
        (sourceJetTerms p q j).length ≤ C*N^C ∧
        ∀ z : ℂ × (Fin N → ℂ), (∀ i, (z.1,z.2 i) ∈ U) → (z.1,z.2 p,z.2 q) ∈ P →
          CoefficientPoint p q z ∧ ∀ T ∈ sourceJetTerms p q j,
            JetBound T.regularPart z r ((C:ℝ)*N^C) := by
  obtain ⟨D,hD,U,P,hU,hsU,hP,hsP,hscalar⟩ := scalar_bounds_uniform s c hs hS hc (j+r+1)
  let B := fieldBoundConstant (j+r) D
  let H := stepScale (j+r) (2*j) B
  obtain ⟨L,hL⟩ := exists_nat_gt (H^j)
  obtain ⟨K,hK,hcount⟩ := sourceJetTerms_source_bound j
  let C : ℕ := K+L+4*j+1
  have hKC : K ≤ C := by dsimp [C]; omega
  have hdC : 4*j ≤ C := by dsimp [C]; omega
  have hHC : H^j ≤ (C:ℝ) := hL.le.trans (by exact_mod_cast (show L ≤ C by dsimp [C]; omega))
  refine ⟨C,by dsimp [C]; omega,U,P,hU,hsU,hP,hsP,?_⟩
  intro N hN p q _hpq
  refine ⟨(hcount N hN p q).trans ?_,?_⟩
  · gcongr
  · intro z hz hp
    have h := hscalar N p q z hz hp
    refine ⟨h.coefficient,?_⟩
    intro T hT
    apply (generated_regularPart_bound p q j r z D hN h T hT).mono le_rfl
    change H^j*(N:ℝ)^(4*j) ≤ (C:ℝ)*(N:ℝ)^C
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hB : 0 ≤ B := by
      dsimp [B,fieldBoundConstant]
      have : 0 ≤ D := by linarith
      positivity
    have hH : 0 ≤ H := zero_le_one.trans (stepScale_one_le _ _ hB)
    gcongr

end
end IsingBulk.Jets
