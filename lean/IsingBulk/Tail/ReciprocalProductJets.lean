import IsingBulk.Tail.ScaledAnalyticProductJets
import IsingBulk.Tail.CompactAnalyticJetBounds

namespace IsingBulk.Tail
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma analytic_composition_geometric_jets (g : ℂ → ℂ) (f : E → ℂ) (x : E)
    (k : ℕ) (hg : AnalyticAt ℂ g (f x)) (hf : AnalyticAt ℂ f x)
    (C D : ℝ) (hC : ∀ i ≤ k, ‖iteratedFDeriv ℂ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℂ k (g ∘ f) x‖ ≤ k.factorial*C*D^k := by
  let V := {z : ℂ | AnalyticAt ℂ g z}
  have hV : IsOpen V := isOpen_analyticAt ℂ g
  have hfx : f x ∈ V := hg
  have he : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ f y ∧ f y ∈ V :=
    hf.eventually_analyticAt.and (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx))
  obtain ⟨U,hU,hopen,hx⟩ := _root_.eventually_nhds_iff.mp he
  have hgu : ContDiffOn ℂ ω g V := fun z hz => hz.contDiffAt.contDiffWithinAt
  have hfu : ContDiffOn ℂ ω f U := fun y hy => (hU y hy).1.contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_comp_le hgu hfu (n := k) (by simp)
    hV.uniqueDiffOn hopen.uniqueDiffOn (fun y hy => (hU y hy).2) hx
    (C := C) (D := D) (by simpa only [iteratedFDerivWithin_of_isOpen _ hV hfx] using hC)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

lemma reciprocal_one_sub_compact_jets (q : ℝ) (hq : q < 1) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ q → ∀ k ≤ J,
      ‖iteratedFDeriv ℂ k (fun w : ℂ => (1-w)⁻¹) z‖ ≤ C := by
  have ha : AnalyticOnNhd ℂ (fun w : ℂ => (1-w)⁻¹) (closedBall 0 q) := by
    intro z hz
    apply (analyticAt_const.sub analyticAt_id).inv
    have hn : ‖z‖ ≤ q := by simpa [mem_closedBall,dist_eq_norm] using hz
    intro he
    have heq : z=1 := (sub_eq_zero.mp he).symm
    simp only [heq,norm_one] at hn
    linarith
  obtain ⟨r,C,hr,hC,hb⟩ := compact_analytic_jet_bounds _ (isCompact_closedBall 0 q) ha J
  refine ⟨C,hC,?_⟩
  intro z hz k hk
  exact (hb z (by simpa [mem_closedBall,dist_eq_norm] using hz) z (by simpa using hr.le) k hk).1

/-- The constant depends only on fixed derivative order and the named strict
factor q. Dimension, number of factors and derivative scale M come afterwards. -/
theorem reciprocal_product_uniform_jets (q : ℝ) (hq : q < 1) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E],
      ∀ (N : ℕ) (M : ℝ), 1 ≤ M →
      ∀ (f : Fin N → E → ℂ) (x : E),
      (∀ i, AnalyticAt ℂ (f i) x) →
      (∀ i, ∀ k ≤ J, ‖iteratedFDeriv ℂ k (f i) x‖ ≤ M^k) →
      (∃ ell : Fin N, ‖f ell x‖ ≤ q) →
      ∀ k ≤ J, ‖iteratedFDeriv ℂ k (fun y => (1-∏ i, f i y)⁻¹) x‖ ≤
        C*(M*(N:ℝ))^k := by
  obtain ⟨B,hB,hbound⟩ := reciprocal_one_sub_compact_jets q hq J
  refine ⟨J.factorial*B,by positivity,?_⟩
  intro E _ _ N M hM f x ha hj hell k hk
  let F : E → ℂ := fun y => ∏ i, f i y
  have hfa : AnalyticAt ℂ F x := Finset.analyticAt_fun_prod Finset.univ (fun i _ => ha i)
  have hnorm (i : Fin N) : ‖f i x‖ ≤ 1 := by simpa using hj i 0 (Nat.zero_le J)
  obtain ⟨ell,hell⟩ := hell
  have hprod : ‖F x‖ ≤ q := by
    dsimp [F]
    rw [norm_prod,← Finset.mul_prod_erase _ _ (Finset.mem_univ ell)]
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
    simpa [F,mul_comm] using hh
  have hh := analytic_composition_geometric_jets (fun w : ℂ => (1-w)⁻¹) F x k
    houter hfa B (M*(N:ℝ)) (fun i hi => hbound (F x) hprod i (hi.trans hk)) hinner
  change ‖iteratedFDeriv ℂ k ((fun w : ℂ => (1-w)⁻¹) ∘ F) x‖ ≤ _
  exact hh.trans (by gcongr)

end
end IsingBulk.Tail
