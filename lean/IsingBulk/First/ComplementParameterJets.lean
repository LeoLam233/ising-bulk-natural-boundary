import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Fixed-radius parameter derivatives of the exact exponential kernel.
Each derivative increases auxiliary degree by at most one. The complete
coefficient functions are differentiated, including all earlier derivatives. -/
namespace IsingBulk.First
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Topology

structure ParameterExpTerm where
  degree : ℕ
  coefficient : ℂ → ℂ

def ParameterExpTerm.value (T : ParameterExpTerm) (B : ℂ → ℂ) (z s : ℂ) : ℂ :=
  T.coefficient s * z ^ T.degree * Complex.exp (B s * z)

def parameterExpChildren (B : ℂ → ℂ) (T : ParameterExpTerm) : List ParameterExpTerm :=
  [⟨T.degree, deriv T.coefficient⟩,
   ⟨T.degree + 1, fun s => T.coefficient s * deriv B s⟩]

def parameterExpTerms (A B : ℂ → ℂ) : ℕ → List ParameterExpTerm
  | 0 => [⟨0, A⟩]
  | j + 1 => (parameterExpTerms A B j).flatMap (parameterExpChildren B)

def parameterExpSum (B : ℂ → ℂ) (z : ℂ) (L : List ParameterExpTerm) (s : ℂ) : ℂ :=
  (L.map (fun T => T.value B z s)).sum

def parameterExpPolynomial (z : ℂ) (L : List ParameterExpTerm) (s : ℂ) : ℂ :=
  (L.map (fun T => T.coefficient s * z ^ T.degree)).sum

theorem parameterExpSum_eq_polynomial (B : ℂ → ℂ) (z : ℂ)
    (L : List ParameterExpTerm) (s : ℂ) :
    parameterExpSum B z L s = parameterExpPolynomial z L s * Complex.exp (B s * z) := by
  induction L with
  | nil => simp [parameterExpSum, parameterExpPolynomial]
  | cons T L ih =>
    simp only [parameterExpSum, parameterExpPolynomial, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    unfold ParameterExpTerm.value
    ring

/-- Every generated coefficient is analytic wherever the genuine preceding
amplitude and scalar phase are analytic. -/
theorem parameterExpTerms_analytic (A B : ℂ → ℂ) {s : ℂ}
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (j : ℕ) :
    ∀ T ∈ parameterExpTerms A B j, AnalyticAt ℂ T.coefficient s := by
  induction j with
  | zero =>
    intro T hT
    simp only [parameterExpTerms, List.mem_singleton] at hT
    subst T
    exact hA
  | succ j ih =>
    intro T hT
    obtain ⟨U, hU, hT⟩ := List.mem_flatMap.mp hT
    have hreg := ih U hU
    simp only [parameterExpChildren, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact hreg.deriv
    · exact hreg.mul hB.deriv

/-- The auxiliary polynomial degree is at most the derivative order. -/
theorem parameterExpTerms_degree (A B : ℂ → ℂ) (j : ℕ) :
    ∀ T ∈ parameterExpTerms A B j, T.degree ≤ j := by
  induction j with
  | zero =>
    intro T hT
    simp only [parameterExpTerms, List.mem_singleton] at hT
    subst T
    exact le_rfl
  | succ j ih =>
    intro T hT
    obtain ⟨U, hU, hT⟩ := List.mem_flatMap.mp hT
    have hdeg := ih U hU
    simp only [parameterExpChildren, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl <;> simp only <;> omega

/-- The exact derivative of one generated term is the sum of its two children. -/
theorem parameterExpTerm_hasDerivAt (T : ParameterExpTerm) (B : ℂ → ℂ) (z s : ℂ)
    (hT : DifferentiableAt ℂ T.coefficient s) (hB : DifferentiableAt ℂ B s) :
    HasDerivAt (T.value B z) (parameterExpSum B z (parameterExpChildren B T) s) s := by
  have h := (hT.hasDerivAt.mul_const (z ^ T.degree)).mul
    ((hB.hasDerivAt.mul_const z).cexp)
  convert h using 1
  · rfl
  · simp only [parameterExpSum, parameterExpChildren, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ParameterExpTerm.value, pow_succ]
    ring

/-- Differentiation of the complete finite term sum, with no frozen coefficients. -/
theorem parameterExpSum_hasDerivAt (B : ℂ → ℂ) (z s : ℂ) (L : List ParameterExpTerm)
    (hL : ∀ T ∈ L, DifferentiableAt ℂ T.coefficient s) (hB : DifferentiableAt ℂ B s) :
    HasDerivAt (parameterExpSum B z L)
      (parameterExpSum B z (L.flatMap (parameterExpChildren B)) s) s := by
  induction L with
  | nil =>
    change HasDerivAt (fun _ : ℂ => 0) 0 s
    exact hasDerivAt_const s (0 : ℂ)
  | cons T L ih =>
    have ht := parameterExpTerm_hasDerivAt T B z s (hL T (List.mem_cons_self)) hB
    have hl := ih (fun U hU => hL U (List.mem_cons_of_mem T hU))
    change HasDerivAt (fun w => T.value B z w + parameterExpSum B z L w) _ s
    convert ht.add hl using 1
    simp only [parameterExpSum, List.flatMap_cons, List.map_append, List.sum_append]

/-- Actual fixed-parameter complex derivatives equal a polynomial in the
auxiliary variable times the same exponential, on the original open domain. -/
theorem parameter_exponential_derivative (A B : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (j : ℕ) (z : ℂ) : ∀ s ∈ U,
    (deriv^[j] (fun w => A w * Complex.exp (B w * z))) s =
      parameterExpPolynomial z (parameterExpTerms A B j) s * Complex.exp (B s * z) := by
  suffices h : ∀ s ∈ U,
      (deriv^[j] (fun w => A w * Complex.exp (B w * z))) s =
        parameterExpSum B z (parameterExpTerms A B j) s by
    intro s hs
    rw [h s hs, parameterExpSum_eq_polynomial]
  induction j with
  | zero =>
    intro s _
    simp [parameterExpTerms, parameterExpSum, ParameterExpTerm.value]
  | succ j ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    have he : (deriv^[j] (fun w => A w * Complex.exp (B w * z))) =ᶠ[𝓝 s]
        parameterExpSum B z (parameterExpTerms A B j) := by
      filter_upwards [hU.mem_nhds hs] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact (parameterExpSum_hasDerivAt B z s (parameterExpTerms A B j)
      (fun T hT => (parameterExpTerms_analytic A B (hA s hs) (hB s hs) j T hT).differentiableAt)
      (hB s hs).differentiableAt).deriv

end
end IsingBulk.First
