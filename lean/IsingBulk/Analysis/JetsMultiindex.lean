import IsingBulk.Analysis.JetsOneStep
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Coordinate words represent genuine partial derivatives. Parameter letters
can be moved in front by analytic symmetry; they are not scalar order tags. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology

def directionJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (d : ι → E) : List ι → (E → ℂ) → E → ℂ
  | [], f => f
  | a::l, f => fun x => fderiv ℂ (directionJet d l f) x (d a)

theorem directionJet_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (d : ι → E) (l : List ι) (f : E → ℂ) (x : E)
    (hf : AnalyticAt ℂ f x) : AnalyticAt ℂ (directionJet d l f) x := by
  induction l with
  | nil => exact hf
  | cons a l ih =>
    exact ((ContinuousLinearMap.apply ℂ ℂ (d a)).analyticAt _).comp ih.fderiv

theorem directionJet_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (d : ι → E) (l : List ι) (f g : E → ℂ) (x : E)
    (he : f =ᶠ[𝓝 x] g) : directionJet d l f x = directionJet d l g x := by
  induction l generalizing x with
  | nil => exact he.eq_of_nhds
  | cons a l ih =>
    have hh : directionJet d l f =ᶠ[𝓝 x] directionJet d l g := by
      filter_upwards [he.eventually_nhds] with y hy
      exact ih y hy
    exact congrArg (fun F : E →L[ℂ] ℂ => F (d a)) hh.fderiv_eq

theorem directionJet_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (d : ι → E) (a b : ι) (l : List ι) (f : E → ℂ) (x : E)
    (hf : AnalyticAt ℂ f x) :
    directionJet d (a::b::l) f x = directionJet d (b::a::l) f x := by
  have hh := directionJet_analytic d l f x hf
  simp only [directionJet, fderiv_clm_apply hh.fderiv.differentiableAt (differentiableAt_const _),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hh.contDiffAt.isSymmSndFDerivAt_of_omega (d a) (d b)

theorem directionJet_perm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (d : ι → E) {l k : List ι} (hp : l.Perm k)
    (f : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) :
    directionJet d l f x = directionJet d k f x := by
  induction hp generalizing x with
  | nil => rfl
  | @cons a l₁ l₂ hp ih =>
    have he : directionJet d l₁ f =ᶠ[𝓝 x] directionJet d l₂ f := by
      filter_upwards [hf.eventually_analyticAt] with y hy
      exact ih y hy
    exact congrArg (fun F : E →L[ℂ] ℂ => F (d a)) he.fderiv_eq
  | swap a b l => exact directionJet_swap d b a l f x hf
  | trans h1 h2 ih1 ih2 => exact (ih1 x hf).trans (ih2 x hf)

def numeratorDirection {N : ℕ} : Option (Fin N) → ℂ × (Fin N → ℂ)
  | none => (1,0)
  | some i => spatialDirection i

def parameterOrder {N : ℕ} : List (Option (Fin N)) → ℕ
  | [] => 0
  | none::l => parameterOrder l+1
  | some _::l => parameterOrder l

def spatialWord {N : ℕ} : List (Option (Fin N)) → List (Fin N)
  | [] => []
  | none::l => spatialWord l
  | some i::l => i::spatialWord l

theorem mixed_word_degree {N : ℕ} (l : List (Option (Fin N))) :
    parameterOrder l+(spatialWord l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp_all [parameterOrder, spatialWord] <;> omega

theorem mixed_word_canonical_perm {N : ℕ} (l : List (Option (Fin N))) :
    l.Perm (List.replicate (parameterOrder l) none ++ (spatialWord l).map some) := by
  induction l with
  | nil => simp [parameterOrder, spatialWord]
  | cons a l ih =>
    cases a with
    | none => simpa [parameterOrder, spatialWord, List.replicate_succ] using ih.cons none
    | some i =>
      simp only [parameterOrder, spatialWord, List.map_cons]
      exact (ih.cons (some i)).trans (List.perm_middle.symm)

def numeratorJet {N : ℕ} (l : List (Option (Fin N)))
    (Q : ℂ × (Fin N → ℂ) → ℂ) : ℂ × (Fin N → ℂ) → ℂ :=
  directionJet numeratorDirection l Q

/-- The mixed word is exactly the canonical parameter-then-spatial partial
derivative on an analytic numerator. No Vandermonde is divided out. -/
theorem numeratorJet_canonical {N : ℕ} (l : List (Option (Fin N)))
    (Q : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ))
    (hQ : AnalyticAt ℂ Q z) :
    numeratorJet l Q z = numeratorJet
      (List.replicate (parameterOrder l) none ++ (spatialWord l).map some) Q z :=
  directionJet_perm numeratorDirection (mixed_word_canonical_perm l) Q z hQ

def cutoffJet {N : ℕ} : List (Fin N) → ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ
  | [], w => w
  | i::l, w => fun x => fderiv ℝ (cutoffJet l w) x (Pi.single i 1)

def unfactoredNumerator {N : ℕ} (regularFactor : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i : Fin N, ∏ k ∈ Finset.Ioi i, (z.2 i-z.2 k))^2 * regularFactor z

theorem unfactoredNumerator_analytic {N : ℕ}
    (A : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ))
    (hA : AnalyticAt ℂ A z) : AnalyticAt ℂ (unfactoredNumerator A) z := by
  apply AnalyticAt.mul _ hA
  apply AnalyticAt.pow
  apply Finset.analyticAt_fun_prod
  intro i _
  apply Finset.analyticAt_fun_prod
  intro k _
  exact (analytic_coordinate i z).sub (analytic_coordinate k z)

end
end IsingBulk.Jets
