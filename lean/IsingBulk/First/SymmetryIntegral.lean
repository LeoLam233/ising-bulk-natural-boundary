import IsingBulk.First.ContourAngular
import IsingBulk.First.SymmetryAlgebra

/-! Symmetry is proved for the actual normalized iterated contour integrals. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem neg_cons {n : ℕ} (z : ℂ) (x : Fin n → ℂ) :
    (fun i : Fin (n+1) => -(Fin.cons z x : Fin (n+1) → ℂ) i) = (Fin.cons (-z) (fun i => -x i) : Fin (n+1) → ℂ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem star_cons {n : ℕ} (z : ℂ) (x : Fin n → ℂ) :
    (fun i : Fin (n+1) => star ((Fin.cons z x : Fin (n+1) → ℂ) i)) = (Fin.cons (star z) (fun i => star (x i)) : Fin (n+1) → ℂ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem multiCircleIntegral_neg (r : ℝ) (N : ℕ) (f : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun x => f (fun i => -x i)) =
      (-1:ℂ)^N * multiCircleIntegral r N f := by
  induction N with
  | zero =>
    simp only [multiCircleIntegral, pow_zero, one_mul]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let g : (Fin n → ℂ) → ℂ := fun x => normalizedCircleIntegral r (fun w => f (Fin.cons w x))
    change multiCircleIntegral r n (fun x => normalizedCircleIntegral r
      (fun w => f (fun i => -(Fin.cons w x : Fin (n+1) → ℂ) i))) = (-1:ℂ)^(n+1)*multiCircleIntegral r n g
    have hh (x : Fin n → ℂ) : normalizedCircleIntegral r
        (fun w => f (fun i => -(Fin.cons w x : Fin (n+1) → ℂ) i)) = -g (fun i => -x i) := by
      simp only [neg_cons]
      exact normalizedCircleIntegral_neg r (fun w => f (Fin.cons w (fun i => -x i)))
    simp_rw [hh]
    rw [show (fun x : Fin n → ℂ => -g (fun i => -x i)) =
        (fun x : Fin n → ℂ => (-1:ℂ)*g (fun i => -x i)) by
      funext x
      exact (neg_one_mul _).symm]
    rw [multiCircleIntegral_const_mul, ih]
    rw [pow_succ]
    ring

theorem multiCircleIntegral_conjugate (r : ℝ) (N : ℕ) (f : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun x => star (f (fun i => star (x i)))) =
      star (multiCircleIntegral r N f) := by
  induction N with
  | zero =>
    change star (f (fun i => star (Fin.elim0 i))) = star (f Fin.elim0)
    congr 1
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let g : (Fin n → ℂ) → ℂ := fun x => normalizedCircleIntegral r (fun w => f (Fin.cons w x))
    change multiCircleIntegral r n (fun x => normalizedCircleIntegral r
      (fun w => star (f (fun i => star ((Fin.cons w x : Fin (n+1) → ℂ) i))))) = star (multiCircleIntegral r n g)
    have hh (x : Fin n → ℂ) : normalizedCircleIntegral r
        (fun w => star (f (fun i => star ((Fin.cons w x : Fin (n+1) → ℂ) i)))) =
        star (g (fun i => star (x i))) := by
      simp only [star_cons]
      exact normalizedCircleIntegral_conjugate r (fun w => f (Fin.cons w (fun i => star (x i))))
    simp_rw [hh]
    exact ih g

theorem multiCircleIntegral_neg_even (r : ℝ) {N : ℕ} (hN : Even N)
    (f : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun x => f (fun i => -x i)) = multiCircleIntegral r N f := by
  rw [multiCircleIntegral_neg, hN.neg_one_pow, one_mul]

/-- Evenness of the actual fixed-radius even-particle source form factor. -/
theorem doubleFormFactor_even (N : ℕ) (hN : Even N) (r : ℝ) (s : ℂ) :
    doubleFormFactor N r (-s) = doubleFormFactor N r s := by
  unfold doubleFormFactor
  congr 1
  rw [← multiCircleIntegral_neg_even r hN (fun y => multiCircleIntegral r N (fun x => doubleDensity (-s) x y))]
  congr 1
  funext y
  rw [← multiCircleIntegral_neg_even r hN (fun x => doubleDensity (-s) x (fun i => -y i))]
  congr 1
  funext x
  exact doubleDensity_neg hN s x y

/-- Conjugation of argument and value, including circle orientation and every
normalized measure. No pointwise-only replacement is used. -/
theorem doubleFormFactor_conjugate (N : ℕ) (r : ℝ) (s : ℂ) :
    doubleFormFactor N r (star s) = star (doubleFormFactor N r s) := by
  unfold doubleFormFactor
  rw [star_mul]
  have hc : star ((N.factorial : ℂ)⁻¹) = (N.factorial : ℂ)⁻¹ := by simp
  rw [hc]
  conv_rhs => rw [mul_comm]
  congr 1
  rw [← multiCircleIntegral_conjugate]
  congr 1
  funext y
  rw [← multiCircleIntegral_conjugate]
  congr 1
  funext x
  simpa only [star_star] using doubleDensity_conjugate s
    (fun i => star (x i)) (fun i => star (y i))

end
end IsingBulk.First
