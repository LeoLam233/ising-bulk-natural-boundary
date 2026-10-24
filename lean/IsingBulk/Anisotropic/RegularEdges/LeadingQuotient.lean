import IsingBulk.Anisotropic.RegularEdges.PhaseJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Filter
open scoped Topology

/-- Exact analytic numerator of the iterated derivative of a simple quotient. -/
def quotientJetNumerator (A D : ℂ→ℂ) : ℕ→ℂ→ℂ
  | 0 => A
  | n+1 => fun u => D u*deriv (quotientJetNumerator A D n) u-
      (n+1:ℂ)*deriv D u*quotientJetNumerator A D n u

theorem quotientJetNumerator_analyticAt {A D : ℂ→ℂ} {u : ℂ}
    (hA : AnalyticAt ℂ A u) (hD : AnalyticAt ℂ D u) (n : ℕ) :
    AnalyticAt ℂ (quotientJetNumerator A D n) u := by
  induction n with
  | zero => exact hA
  | succ n ih => exact (hD.mul ih.deriv).sub ((analyticAt_const.mul hD.deriv).mul ih)

/-- This identity is a genuine derivative calculation, not a formal pole ansatz. -/
theorem iteratedDeriv_quotient_eq {A D : ℂ→ℂ} {u : ℂ}
    (hA : AnalyticAt ℂ A u) (hD : AnalyticAt ℂ D u) (hne : D u≠0) (n : ℕ) :
    iteratedDeriv n (fun z => A z/D z) u=quotientJetNumerator A D n u/(D u)^(n+1) := by
  induction n generalizing u with
  | zero => simp [quotientJetNumerator]
  | succ n ih =>
    have he : iteratedDeriv n (fun z => A z/D z)=ᶠ[𝓝 u]
        (fun z => quotientJetNumerator A D n z/(D z)^(n+1)) := by
      filter_upwards [hA.eventually_analyticAt,hD.eventually_analyticAt,
        hD.continuousAt.eventually_ne hne] with z ha hd hn
      exact ih ha hd hn
    rw [iteratedDeriv_succ,he.deriv_eq]
    change deriv (quotientJetNumerator A D n / D^(n+1)) u = _
    rw [deriv_div (quotientJetNumerator_analyticAt hA hD n).differentiableAt
      (hD.differentiableAt.pow _) (pow_ne_zero _ hne),deriv_pow hD.differentiableAt]
    simp only [quotientJetNumerator,Pi.pow_apply,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    field_simp
    ring

theorem quotientJetNumerator_at_zero {A D : ℂ→ℂ} {u : ℂ} (hD : D u=0) (n : ℕ) :
    quotientJetNumerator A D n u=(-1:ℂ)^n*(n.factorial:ℂ)*(deriv D u)^n*A u := by
  induction n with
  | zero => simp [quotientJetNumerator]
  | succ n ih =>
    simp only [quotientJetNumerator,hD,zero_mul,zero_sub,ih,Nat.factorial_succ,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

end
end IsingBulk.Anisotropic.RegularEdges
