import IsingBulk.Analysis.JetsCoefficientJets

/-! The complete canceled pair on a joint parameter/regular-coordinate
neighborhood. The strict B×B bound is a consequence of its double zero;
raw angle derivatives are deliberately not asserted. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Filter
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def branchCompletePair (z : ℂ × ℂ × ℂ) : ℂ :=
  (z.2.1-z.2.2)^2 * regularPairCoefficient z.1 z.2.1 z.2.2

theorem branchCompletePair_analytic (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ branchCompletePair (s,0,0) := by
  exact (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.2.1-z.2.2)^2)
    (s,0,0) by fun_prop).mul (regularPairCoefficient_joint_analytic s c hs hS hc)

/-- Arbitrary fixed strict slack may be chosen before the parameter,
particle number, occupancy or regular coordinates vary. -/
theorem branchCompletePair_strict_neighborhood (s : ℂ) (c q : ℝ)
    (hs : s ≠ 0) (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (hq : 0 < q) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ × ℂ × ℂ,
      dist z (s,0,0) < r → ‖branchCompletePair z‖ < q := by
  have hcont := (branchCompletePair_analytic s c hs hS hc).continuousAt.norm
  have hzero : ‖branchCompletePair (s,0,0)‖ < q := by
    simpa [branchCompletePair] using hq
  have he := hcont.eventually_lt continuousAt_const hzero
  exact Metric.eventually_nhds_iff.mp he

/-- Every prescribed finite regular jet has a common neighborhood bound.
No uniform raw branch-angle jet bound follows or is used here. -/
theorem branchCompletePair_finite_jets (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (s,0,0), ∀ k ≤ j,
      ‖iteratedFDeriv ℂ k branchCompletePair z‖ ≤ C :=
  finite_analytic_jets_bounded _ _ (branchCompletePair_analytic s c hs hS hc) j

/-- Equality to the original complete rational pair away from the removable
reciprocal-root hypersurface. The analytic expression above provides its
continuation on that hypersurface, including a full collision. -/
theorem branchCompletePair_eq_rational (s p q : ℂ)
    (hd : 1-(regularY s p*regularY s q)⁻¹ ≠ 0)
    (hsum : p+q ≠ 0) (hJ : exponentialQuotient (p+q) ≠ 0) :
    branchCompletePair (s,p,q) =
      -(regularY s p-regularY s q)^2 * Complex.exp (-Complex.I*p) *
        Complex.exp (-Complex.I*q) /
        (regularY s p*regularY s q*
          (1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q))^2) :=
  (regular_pair_cancellation s p q hd hsum hJ).symm

end
end IsingBulk.Tail
