import IsingBulk.Analysis.JetsTermPullback

/-! Finite-sum linearity needed to iterate the proved single-term recurrence.
The hypotheses are differentiability, not derivative identities. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Lie

theorem lieStep_finite_sum {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (L : List (ℂ → AngularSpace n → ℂ)) (s : ℂ) (x : AngularSpace n)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hS : ∀ A ∈ L, DifferentiableAt ℂ (fun t => A t x) s)
    (hX : ∀ A ∈ L, DifferentiableAt ℝ (A s) x) :
    DifferentiableAt ℂ (fun t => (L.map (fun A => A t x)).sum) s ∧
      DifferentiableAt ℝ (fun y => (L.map (fun A => A s y)).sum) x ∧
      lieStep V (fun t y => (L.map (fun A => A t y)).sum) s x =
        (L.map (fun A => lieStep V A s x)).sum := by
  induction L with
  | nil => simp [lieStep, divergence, differentiableAt_const]
  | cons A L ih =>
    have hAs := hS A (by simp)
    have hAx := hX A (by simp)
    obtain ⟨hLs,hLx,hL⟩ := ih (fun B h => hS B (by simp [h]))
      (fun B h => hX B (by simp [h]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hAs.fun_add hLs,hAx.fun_add hLx,?_⟩
    have hsprod : ∀ i, DifferentiableAt ℝ (fun y => V s y i*A s y) x :=
      fun i => (hV i).mul hAx
    have hlprod : ∀ i, DifferentiableAt ℝ
        (fun y => V s y i*(L.map (fun B => B s y)).sum) x := fun i => (hV i).mul hLx
    have he : lieStep V (fun t y => A t y+(L.map (fun B => B t y)).sum) s x =
        lieStep V A s x+lieStep V (fun t y => (L.map (fun B => B t y)).sum) s x := by
      simp only [lieStep, divergence, deriv_fun_add hAs hLs, mul_add]
      simp_rw [fderiv_fun_add (hsprod _) (hlprod _)]
      simp only [add_apply, Finset.sum_add_distrib]
      ring
    rw [he, hL]

end
end IsingBulk.Jets
