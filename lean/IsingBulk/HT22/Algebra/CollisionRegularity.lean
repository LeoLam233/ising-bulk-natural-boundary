import IsingBulk.HT22.Algebra.LastBordered
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.Constructions

/-! # Regularity of the explicit full collision quotient

All regularity comes from the actual rational quotient. No analyticity or
bounded-jet premise for a manufactured descendant is introduced.
-/
namespace IsingBulk.HT22.Algebra
noncomputable section
open scoped BigOperators ContDiff

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pair quotient is smooth wherever its actual denominators are nonzero. -/
theorem pairQuotient_contDiffAt {k : WithTop ℕ∞} {x : E}
    (yi yj zi zj : E → ℂ)
    (hyi : ContDiffAt ℝ k yi x) (hyj : ContDiffAt ℝ k yj x)
    (hzi : ContDiffAt ℝ k zi x) (hzj : ContDiffAt ℝ k zj x)
    (hi : yi x ≠ 0) (hj : yj x ≠ 0) (hden : 1-zi x*zj x ≠ 0) :
    ContDiffAt ℝ k (fun u => pairQuotient (yi u) (yj u) (zi u) (zj u)) x := by
  unfold pairQuotient
  simp only [div_eq_mul_inv]
  exact ((hzi.mul (hyi.inv hi)).neg.mul (hzj.mul (hyj.inv hj))).mul
    (((contDiffAt_const.sub (hzi.mul hzj)).pow 2).inv (pow_ne_zero _ hden))

/-- The full squared-Vandermonde quotient has real smooth fixed-order jets,
including at collisions, with only off-diagonal gap assumptions. -/
theorem collisionQuotient_contDiffAt {N : ℕ} {k : WithTop ℕ∞} {x : E}
    (y z : E → Fin N → ℂ)
    (hy : ∀ i, ContDiffAt ℝ k (fun u => y u i) x)
    (hz : ∀ i, ContDiffAt ℝ k (fun u => z u i) x)
    (hne : ∀ i, y x i ≠ 0)
    (hden : ∀ i j, i ≠ j → 1-z x i*z x j ≠ 0) :
    ContDiffAt ℝ k (fun u => collisionQuotient (y u) (z u)) x := by
  unfold collisionQuotient
  apply contDiffAt_prod
  intro i _
  apply contDiffAt_prod
  intro j hj
  exact pairQuotient_contDiffAt _ _ _ _ (hy i) (hy j) (hz i) (hz j)
    (hne i) (hne j) (hden i j (ne_of_lt (Finset.mem_Ioi.mp hj)))

end Smooth

section Analytic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The same literal quotient is holomorphic on its rational regular locus. -/
theorem pairQuotient_analyticAt {x : E} (yi yj zi zj : E → ℂ)
    (hyi : AnalyticAt ℂ yi x) (hyj : AnalyticAt ℂ yj x)
    (hzi : AnalyticAt ℂ zi x) (hzj : AnalyticAt ℂ zj x)
    (hi : yi x ≠ 0) (hj : yj x ≠ 0) (hden : 1-zi x*zj x ≠ 0) :
    AnalyticAt ℂ (fun u => pairQuotient (yi u) (yj u) (zi u) (zj u)) x := by
  exact ((hzi.div hyi hi).neg.mul (hzj.div hyj hj)).div
    ((analyticAt_const.sub (hzi.mul hzj)).pow 2) (pow_ne_zero _ hden)

/-- Full holomorphic collision quotient at every finite order. -/
theorem collisionQuotient_analyticAt {N : ℕ} {x : E}
    (y z : E → Fin N → ℂ)
    (hy : ∀ i, AnalyticAt ℂ (fun u => y u i) x)
    (hz : ∀ i, AnalyticAt ℂ (fun u => z u i) x)
    (hne : ∀ i, y x i ≠ 0)
    (hden : ∀ i j, i ≠ j → 1-z x i*z x j ≠ 0) :
    AnalyticAt ℂ (fun u => collisionQuotient (y u) (z u)) x := by
  unfold collisionQuotient
  apply Finset.analyticAt_fun_prod
  intro i _
  apply Finset.analyticAt_fun_prod
  intro j hj
  exact pairQuotient_analyticAt _ _ _ _ (hy i) (hy j) (hz i) (hz j)
    (hne i) (hne j) (hden i j (ne_of_lt (Finset.mem_Ioi.mp hj)))

end Analytic
end
end IsingBulk.HT22.Algebra
