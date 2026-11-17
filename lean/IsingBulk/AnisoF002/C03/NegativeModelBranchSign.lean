import IsingBulk.AnisoF002.C03.NegativeCenterPeriod
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The physical square-root factor is one common sign

The branch-sensitive center/period identity does not permit independent
particle signs.  On one connected neighborhood the continuous physical
square root differs from the principal square root by one constant sign.
The actual negative-edge hypothesis `Im B(0) < 0` gives the required slit
neighborhood; no principal-branch physical premise is introduced.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter Angular
open scoped Topology

theorem physical_root_branch_sign_constant {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPreconnected U) {b B : X → ℂ}
    (hcB : ContinuousOn B U) (hcb : ContinuousOn b U)
    (hslit : ∀ x ∈ U, B x ∈ Complex.slitPlane)
    (hsq : ∀ x ∈ U, b x ^ 2 = B x) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∀ x ∈ U, Complex.sqrt (B x) / b x = Complex.sqrt (B x₀) / b x₀ := by
  have hbn : ∀ x ∈ U, b x ≠ 0 := by
    intro x hx he
    have hh := hsq x hx
    rw [he, zero_pow two_ne_zero] at hh
    exact Complex.slitPlane_ne_zero (hslit x hx) hh.symm
  have hcs : ContinuousOn (fun x => Complex.sqrt (B x)) U := by
    intro x hx
    exact (Complex.continuousAt_sqrt ((hslit x hx).imp le_of_lt id)).comp_continuousWithinAt
      (hcB x hx)
  have hcf : ContinuousOn (fun x => Complex.sqrt (B x) / b x) U := hcs.div hcb hbn
  have hm : MapsTo (fun x => Complex.sqrt (B x) / b x) U ({1, -1} : Set ℂ) := by
    intro x hx
    have hh := physical_root_branch_sign_sq (Complex.slitPlane_ne_zero (hslit x hx)) (hsq x hx)
    have he := eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (B x) / b x) (1 : ℂ)
      (by simpa using hh)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he
  intro x hx
  exact hU.constant_of_mapsTo ((Set.finite_singleton (-1 : ℂ)).insert 1).isDiscrete
    hcf hm hx hx₀

theorem exists_common_physical_root_sign {b B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hb : AnalyticAt ℂ b 0)
    (hslit : B 0 ∈ Complex.slitPlane) (hsq : ∀ t, b t ^ 2 = B t) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Metric.ball (0 : ℂ) r,
      Complex.sqrt (B t) / b t = Complex.sqrt (B 0) / b 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), B t ∈ Complex.slitPlane :=
    hB.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hslit)
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp
    (hB.eventually_analyticAt.and (hb.eventually_analyticAt.and hev))
  refine ⟨r, hr, ?_⟩
  apply physical_root_branch_sign_constant (convex_ball (0 : ℂ) r).isPreconnected
    (fun t ht => (hall ht).1.continuousAt.continuousWithinAt)
    (fun t ht => (hall ht).2.1.continuousAt.continuousWithinAt)
    (fun t ht => (hall ht).2.2) (fun t _ => hsq t) (Metric.mem_ball_self hr)

/-- The normalized root already constructed in the actual negative chart has
one fixed sign for every sufficiently close center, before the particle
number and derivative order are chosen. -/
theorem exists_common_normalized_physical_root_sign {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hside : (B 0).im < 0)
    {b₀ : ℂ} (hb₀ : b₀ ^ 2 = B 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Metric.ball (0 : ℂ) r,
      Complex.sqrt (B t) / normalizedLocalSquareRoot B b₀ t = Complex.sqrt (B 0) / b₀ := by
  have hslit : B 0 ∈ Complex.slitPlane := Or.inr (ne_of_lt hside)
  have hB0 := Complex.slitPlane_ne_zero hslit
  simpa only [normalizedLocalSquareRoot_center b₀ hB0] using
    exists_common_physical_root_sign hB (normalizedLocalSquareRoot_analyticAt b₀ hB hB0)
      hslit (normalizedLocalSquareRoot_sq hB0 hb₀)

end
end IsingBulk.AnisoF002.NegativeHT
