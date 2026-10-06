import IsingBulk.First.FormFactorNormalization
import IsingBulk.Algebra.PrimeTheorem

/-! Narrow explicit boundary for the published fixed-even-order input.
Tracy--Widom, J. Stat. Phys. 156 (2014), 1125--1135,
DOI 10.1007/s10955-014-1061-4, equation (3), p.1127 and Lemma 3, p.1131.
The observable is the actual full-site normalized contour coefficient.
There is no project-wide external axiom. The external result is a local input.
-/
namespace IsingBulk.First
noncomputable section

/-- Exact fixed-order consequence of the published local smoothness argument.
The radius threshold is allowed to depend on s, as in the published statement.
The derivative is taken with that radius fixed. This is not an offsite bound. -/
def PublishedFullSiteBounded (N : ℕ) (s₀ : ℂ) : Prop :=
  ∀ j : ℕ, ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
    ∀ s : ℂ, ‖s - s₀‖ < δ → 1 < ‖s‖ →
      ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ ∀ r : ℝ, r₀ < r → r < 1 →
        ‖(deriv^[j] (standardFormFactor N r)) s‖ ≤ C

/-- The manuscript's legitimate external theorem parameter at one unit point.
It contains only the published full-site non-Nickel result; neither onsite nor
selected-order complement estimates nor an internal FIRST conclusion are fields. -/
def PublishedTWFixedOrderInput (s₀ : ℂ) : Prop :=
  ‖s₀‖ = 1 → ∀ N : ℕ, 0 < N → Even N → ¬ PrimeFamily.NickelAt s₀ N →
    PublishedFullSiteBounded N s₀

/-- Frozen arithmetic supplies every lower-order non-Nickel hypothesis.
Transferring this full-site bound to T_N still requires the proved onsite bridge
and radius-locality theorem; no such internal conclusion is asserted here. -/
theorem selected_lower_fullSite_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) :
    ∀ N : ℕ, 0 < N → Even N → N < 2*p →
      PublishedFullSiteBounded N (PrimeFamily.selectedPoint p a b) := by
  intro N hN he hlt
  have hn := (PrimeFamily.first_even_Nickel_order hp (by omega) ha hb).2 N hN he hlt
  exact hTW (by
    unfold PrimeFamily.selectedPoint
    exact Complex.norm_exp_ofReal_mul_I _) N hN he hn

end
end IsingBulk.First
