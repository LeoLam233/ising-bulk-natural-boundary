import IsingBulk.First.AnnulusContour

/-! Radius independence of the actual normalized finite product contour,
proved by finitely many one-coordinate annulus moves. -/
namespace IsingBulk.First
noncomputable section

 theorem variableCircleIntegral_const_eq {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ f x) :
    variableCircleIntegral (fun _ : Fin N => R) f =
      variableCircleIntegral (fun _ : Fin N => r) f := by
  classical
  cases N with
  | zero =>
    have he : (fun _ : Fin 0 => R) = (fun _ : Fin 0 => r) := Subsingleton.elim _ _
    rw [he]
  | succ n =>
    let U : Finset (Fin (n+1)) → Fin (n+1) → ℝ := fun t i => if i ∈ t then R else r
    have hU (t : Finset (Fin (n+1))) : ∀ i, r ≤ U t i ∧ U t i ≤ R := by
      intro i
      by_cases hi : i ∈ t
      · simp only [U, ite_eq_left hi]
        exact ⟨hR, le_rfl⟩
      · simp only [U, ite_eq_right hi]
        exact ⟨le_rfl, hR⟩
    have ht : ∀ t : Finset (Fin (n+1)), variableCircleIntegral (U t) f =
        variableCircleIntegral (U ∅) f := by
      intro t
      induction t using Finset.induction_on with
      | empty => rfl
      | @insert i t hit ih =>
        have he : U (insert i t) = Function.update (U t) i R := by
          funext j
          by_cases hj : j=i
          · subst j
            simp [U]
          · simp [U, hj]
        rw [he, variableCircleIntegral_update hr f hf (U t) (hU t) i R (hU t i).2 le_rfl]
        exact ih
    simpa only [U, Finset.mem_univ, ite_true, Finset.notMem_empty, ite_false] using ht Finset.univ

/-- A faithful common-radius contour comparison under actual holomorphy
throughout the annular product. -/
theorem multiCircleIntegral_radius_eq (N : ℕ) {r R : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ x ∈ annularProduct N r R, DifferentiableAt ℂ f x) :
    multiCircleIntegral R N f = multiCircleIntegral r N f := by
  have hcR := variableCircleIntegrand_continuous hr f hf (fun _ => R) (fun _ => ⟨hR, le_rfl⟩)
  have hcr := variableCircleIntegrand_continuous hr f hf (fun _ => r) (fun _ => ⟨le_rfl, hR⟩)
  rw [← variableCircleIntegral_const_radius N R f hcR,
    ← variableCircleIntegral_const_radius N r f hcr]
  exact variableCircleIntegral_const_eq hr hR f hf

end
end IsingBulk.First
