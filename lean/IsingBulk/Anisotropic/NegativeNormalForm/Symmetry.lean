import IsingBulk.Anisotropic.NegativeNormalForm.Algebra

/-! Permutation equivariance of the actual projection and mean correction. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

def permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) : Config n := v ∘ e

@[simp] theorem quadratic_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) :
    quadratic (permute e v) = quadratic v :=
  Equiv.sum_comp e (fun i => v i ^ 2)

@[simp] theorem pairing_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v w : Config n) :
    pairing (permute e v) (permute e w) = pairing v w :=
  Equiv.sum_comp e (fun i => v i * w i)

@[simp] theorem mean_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) :
    mean (permute e v) = mean v := by
  unfold mean permute
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e v]

theorem project_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (v : Config n) :
    project (permute e v) = permute e (project v) := by
  funext i
  simp only [project, mean_permute]
  rfl

@[simp] theorem rankOneCoefficient_permute {n : ℕ}
    (e : Equiv.Perm (Fin n)) (ell : Config n) :
    rankOneCoefficient (permute e ell) = rankOneCoefficient ell := by
  simp [rankOneCoefficient]

theorem meanCorrection_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (ell w : Config n) :
    meanCorrection (permute e ell) (permute e w) = permute e (meanCorrection ell w) := by
  funext i
  simp only [meanCorrection, rankOneCoefficient_permute, pairing_permute]
  rfl

/-- Permutation equivariance forces equality of components on each coincidence
hyperplane. This is the algebraic input to holomorphic divisor preservation. -/
theorem equivariant_coincidence {n : ℕ} (f : Config n → Config n)
    (hf : ∀ (e : Equiv.Perm (Fin n)) v, f (permute e v) = permute e (f v))
    (v : Config n) (i j : Fin n) (hij : v i = v j) : f v i = f v j := by
  have hv : permute (Equiv.swap i j) v = v := by
    funext k
    simp only [permute, Function.comp_apply]
    by_cases hki : k = i
    · subst k; simp [hij]
    by_cases hkj : k = j
    · subst k; simp [hij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := congrFun (hf (Equiv.swap i j) v) i
  rw [hv] at h
  simpa [permute] using h

end
end IsingBulk.Anisotropic.NegativeNormalForm
