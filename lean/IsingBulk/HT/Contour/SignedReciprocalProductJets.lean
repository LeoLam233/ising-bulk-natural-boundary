import IsingBulk.Tail.ReciprocalProductJets

/-! Unit-phase twists preserve the actual polynomial-in-N reciprocal-product
jet estimate. The strict root anchor and all physical product jets remain
explicit; the constant is chosen before the phase and particle number. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Tail Set Filter Metric
open scoped Topology ContDiff BigOperators

theorem signed_reciprocal_product_uniform_jets (q : ℝ) (hq : q < 1) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E],
      ∀ (σ : ℂ), ‖σ‖ = 1 → ∀ (N : ℕ) (M : ℝ), 1 ≤ M →
      ∀ (f : Fin N → E → ℂ) (x : E),
      (∀ i, AnalyticAt ℂ (f i) x) →
      (∀ i, ∀ k ≤ J, ‖iteratedFDeriv ℂ k (f i) x‖ ≤ M^k) →
      (∃ ell : Fin N, ‖f ell x‖ ≤ q) →
      ∀ k ≤ J, ‖iteratedFDeriv ℂ k (fun y => (1-σ*(∏ i, f i y))⁻¹) x‖ ≤
        C*(M*(N:ℝ))^k := by
  obtain ⟨B,hB,hbound⟩ := reciprocal_one_sub_compact_jets q hq J
  refine ⟨J.factorial*B,by positivity,?_⟩
  intro E _ _ σ hσ N M hM f x ha hj hell k hk
  let P : E → ℂ := fun y => ∏ i, f i y
  let F : E → ℂ := fun y => σ*P y
  have hpa : AnalyticAt ℂ P x := Finset.analyticAt_fun_prod Finset.univ (fun i _ => ha i)
  have hfa : AnalyticAt ℂ F x := analyticAt_const.mul hpa
  have hnorm (i : Fin N) : ‖f i x‖ ≤ 1 := by simpa using hj i 0 (Nat.zero_le J)
  obtain ⟨ell,hell⟩ := hell
  have hprod : ‖F x‖ ≤ q := by
    dsimp [F,P]
    rw [norm_mul,hσ,one_mul,norm_prod,← Finset.mul_prod_erase _ _ (Finset.mem_univ ell)]
    have hother : ∏ i ∈ Finset.univ.erase ell, ‖f i x‖ ≤ (1:ℝ) :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hnorm i)
    exact (mul_le_of_le_one_right (norm_nonneg _) hother).trans hell
  have hne : (1-F x) ≠ 0 := by
    intro he
    have heq : F x=1 := (sub_eq_zero.mp he).symm
    rw [heq,norm_one] at hprod
    linarith
  have houter : AnalyticAt ℂ (fun w : ℂ => (1-w)⁻¹) (F x) :=
    (analyticAt_const.sub analyticAt_id).inv hne
  have hinner : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i F x‖ ≤ (M*(N:ℝ))^i := by
    intro i hi hik
    have hh := analytic_finset_product_geometric_jets Finset.univ f x J 1 M (by norm_num)
      (by linarith) (fun j _ => ha j) (fun j _ r hr => by simpa using hj j r hr) i (hik.trans hk)
    have he : F=σ • P := rfl
    rw [he,iteratedFDeriv_const_smul_apply hpa.contDiffAt,norm_smul,hσ,one_mul]
    simpa [P,mul_comm] using hh
  have hh := analytic_composition_geometric_jets (fun w : ℂ => (1-w)⁻¹) F x k
    houter hfa B (M*(N:ℝ)) (fun i hi => hbound (F x) hprod i (hi.trans hk)) hinner
  change ‖iteratedFDeriv ℂ k ((fun w : ℂ => (1-w)⁻¹) ∘ F) x‖ ≤ _
  exact hh.trans (by gcongr)

end
end IsingBulk.HT.Contour
