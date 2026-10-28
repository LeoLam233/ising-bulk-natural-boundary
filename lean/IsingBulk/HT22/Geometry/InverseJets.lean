import IsingBulk.HT22.Geometry.RegularInverse

/-! Genuine fixed-v and fixed-t partial derivatives of the F001 inverse. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter

def inverseV (t v : ℂ) : ℂ := deriv (regularInverse t) v
def inverseT (t v : ℂ) : ℂ := deriv (fun s => regularInverse s v) t

def inverseVJoint (z : ℂ × ℂ) : ℂ :=
  fderiv ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) z (0, 1)

def inverseTJoint (z : ℂ × ℂ) : ℂ :=
  fderiv ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) z (1, 0)

theorem inverseVJoint_eq (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t, v)) :
    inverseVJoint (t, v) = inverseV t v := by
  have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v t).prodMk (hasDerivAt_id v))
  simpa only [inverseVJoint, inverseV, Function.comp_def] using hd.deriv.symm

theorem inverseTJoint_eq (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t, v)) :
    inverseTJoint (t, v) = inverseT t v := by
  have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t v))
  simpa only [inverseTJoint, inverseT, Function.comp_def, id_eq] using hd.deriv.symm

theorem inverseV_joint_analytic (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t, v)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => inverseV z.1 z.2) (t, v) := by
  have hJ : AnalyticAt ℂ inverseVJoint (t, v) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hU.fderiv
  apply hJ.congr
  filter_upwards [hU.eventually_analyticAt] with z hz
  exact inverseVJoint_eq z.1 z.2 hz

theorem inverseT_joint_analytic (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t, v)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => inverseT z.1 z.2) (t, v) := by
  have hJ : AnalyticAt ℂ inverseTJoint (t, v) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp hU.fderiv
  apply hJ.congr
  filter_upwards [hU.eventually_analyticAt] with z hz
  exact inverseTJoint_eq z.1 z.2 hz

/-- Each fixed joint jet is bounded on a compact actual branch-domain set.
No constant uniform over all derivative orders is asserted. -/
theorem regularInverse_compact_jets (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hU : ∀ z ∈ K, AnalyticAt ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) z)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      ‖iteratedFDeriv ℂ j (fun p : ℂ × ℂ => regularInverse p.1 p.2) z‖ ≤ C := by
  have ha : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) K := hU
  have hcont : ContinuousOn
      (iteratedFDeriv ℂ j (fun p : ℂ × ℂ => regularInverse p.1 p.2)) K := by
    intro z hz
    exact ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro z hz
  exact (hC z hz).trans (by have := le_max_left C 0; linarith)

end
end IsingBulk.HT22.Geometry
