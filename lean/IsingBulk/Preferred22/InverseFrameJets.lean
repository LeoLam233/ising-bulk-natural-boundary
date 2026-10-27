import IsingBulk.Preferred22.RegularFrameJets
import IsingBulk.Preferred22.SeparatedWords

/-! Uniform analytic jets of the literal inverse-chart multipliers that
appear when the true source frames act on real angular factors. -/
set_option maxHeartbeats 800000

namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- One fixed compact source tube controls all fixed-order Uq and Udot
jets. The domain is chosen before derivative order and particle number. -/
theorem preferred_inverse_domain_all_jets (d : PreferredBranchData) (ρ : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D)
    (hU : ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    ∀ j : ℕ, ∃ C : ℝ, 1≤C ∧
      ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D →
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (s,q)‖≤C ∧
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) (s,q)‖≤C := by
  let K := Metric.closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D
  have hK : IsCompact K := (isCompact_closedBall _ _).prod hD
  have hqa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact preferredSourceUQ_analyticAt_of_joint z.1 z.2 (hU _ _ (by linarith) hz.2)
  have hsa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact preferredSourceUDot_analyticAt_of_joint z.1 z.2 (hU _ _ (by linarith) hz.2)
  intro j
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (fun z hz =>
    ((hqa.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (fun z hz =>
    ((hsa.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  refine ⟨max 1 (max A B),le_max_left _ _,?_⟩
  intro s q hs hq
  have hz : (s,q)∈K := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq⟩
  exact ⟨(hA _ hz).trans ((le_max_left A B).trans (le_max_right _ _)),
    (hB _ hz).trans ((le_max_right A B).trans (le_max_right _ _))⟩

theorem preferred_inverse_domain_finite_jets (d : PreferredBranchData) (ρ : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D)
    (hU : ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D →
      ∀ j≤J,
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (s,q)‖≤C ∧
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) (s,q)‖≤C := by
  choose A hA hjet using preferred_inverse_domain_all_jets d ρ D hρ hD hU
  let C := 1+∑ j∈Finset.range (J+1), A j
  have hsum : 0≤∑ j∈Finset.range (J+1), A j :=
    Finset.sum_nonneg (fun j _ => zero_le_one.trans (hA j))
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro s q hs hq j hj
  have hAj : A j≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => zero_le_one.trans (hA k))
      (show j∈Finset.range (J+1) by simp; omega)
    dsimp [C]
    linarith
  exact ⟨((hjet j s q hs hq).1).trans hAj,((hjet j s q hs hq).2).trans hAj⟩

/-- Projection to one actual coordinate has operator norm at most one,
so the inverse multiplier's joint jet bound does not grow with N. -/
theorem preferredSeparatedInverseFactor_jet_le {N : ℕ} (a : Option (Fin N)) (b : Fin N)
    (z : ℂ × (Fin N → ℂ)) (j : ℕ) {C : ℝ} (hC : 0≤C)
    (hU : ∀ i, AnalyticAt ℂ (fun y : ℂ × ℂ => preferredMovingInverse y.1 y.2) (z.1,z.2 i))
    (hjet : ∀ i,
      ‖iteratedFDeriv ℂ j (fun y : ℂ × ℂ => preferredSourceUQ y.1 y.2) (z.1,z.2 i)‖≤C ∧
      ‖iteratedFDeriv ℂ j (fun y : ℂ × ℂ => preferredSourceUDot y.1 y.2) (z.1,z.2 i)‖≤C) :
    ‖iteratedFDeriv ℂ j (preferredSeparatedInverseFactor a b) z‖≤C := by
  have hproj (i : Fin N) (f : ℂ × ℂ → ℂ) (hf : AnalyticAt ℂ f (z.1,z.2 i))
      (hb : ‖iteratedFDeriv ℂ j f (z.1,z.2 i)‖≤C) :
      ‖iteratedFDeriv ℂ j (fun y : ℂ × (Fin N → ℂ) => f (y.1,y.2 i)) z‖≤C := by
    change ‖iteratedFDeriv ℂ j (f ∘ preferredOneProjection i) z‖≤C
    rw [analytic_iteratedFDeriv_comp_linear (preferredOneProjection i) f z hf j]
    have hL : ‖preferredOneProjection i‖≤1 :=
      (preferredOneProjection i).opNorm_le_bound zero_le_one (fun y => by
        simpa only [one_mul] using preferredOneProjection_norm_le i y)
    apply ((iteratedFDeriv ℂ j f (z.1,z.2 i)).norm_compContinuousLinearMap_le _).trans
    apply (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
    exact mul_le_of_le_one_right hC (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL))
  cases a with
  | none =>
    change ‖iteratedFDeriv ℂ j (fun y : ℂ × (Fin N → ℂ) => preferredSourceUDot y.1 (y.2 b)) z‖≤C
    exact hproj b (fun y : ℂ × ℂ => preferredSourceUDot y.1 y.2)
      (preferredSourceUDot_analyticAt_of_joint _ _ (hU b)) (hjet b).2
  | some a =>
    change ‖iteratedFDeriv ℂ j (fun y : ℂ × (Fin N → ℂ) => if b=a then preferredSourceUQ y.1 (y.2 a) else 0) z‖≤C
    by_cases hba : b=a
    · simp only [hba,ite_true]
      exact hproj a (fun y : ℂ × ℂ => preferredSourceUQ y.1 y.2)
        (preferredSourceUQ_analyticAt_of_joint _ _ (hU a)) (hjet a).1
    · simp only [hba,ite_false]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero,norm_zero] using hC
      | succ j => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using hC

end
end IsingBulk.Preferred22
