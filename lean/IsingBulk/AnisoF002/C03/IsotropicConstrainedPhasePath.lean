import IsingBulk.AnisoF002.C03.IsotropicActualExtremeProjection
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The genuine constrained phase path at every point of a fiber

The previously constructed derivative is translated to every point of
the original constraint-preserving angular line. The physical phase and
the entire changing populations are reevaluated at that point.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem constrainedAngleLine_add {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (a t : ℝ) :
    constrainedAngleLine (constrainedAngleLine θ i j a) i j t =
      constrainedAngleLine θ i j (a + t) := by
  simp only [constrainedAngleLine, add_smul, add_assoc]

theorem constrainedAngleLine_first {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j) (t : ℝ) :
    constrainedAngleLine θ i j t i = θ i + t := by
  simp only [constrainedAngleLine, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hij, sub_zero, smul_eq_mul, mul_one]

theorem constrainedAngleLine_last {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (hij : i ≠ j) (t : ℝ) :
    constrainedAngleLine θ i j t j = θ j - t := by
  simp only [constrainedAngleLine, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hij), zero_sub, smul_eq_mul, mul_neg, mul_one]
  ring

theorem constrainedAngleLine_other {N : ℕ} (θ : Fin N → ℝ) (i j k : Fin N)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) :
    constrainedAngleLine θ i j t k = θ k := by
  simp only [constrainedAngleLine, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_self, smul_eq_mul, mul_zero, add_zero]

theorem actualTotalPhase_constrainedLine_hasDerivAt_any {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    HasDerivAt (fun u : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j u))
      (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
        actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j) t := by
  have hh := actualTotalPhase_constrainedLine_hasDerivAt s hs η τ ξ hη hτ hξ
    (constrainedAngleLine θ i j t) i j
  have hh' : HasDerivAt
      (fun u : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine (constrainedAngleLine θ i j t) i j u))
      (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
        actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j) (t - t) := by
    simpa only [sub_self] using hh
  have hshift := hh'.comp_sub_const t t
  simpa only [constrainedAngleLine_add, ← add_sub_assoc, add_sub_cancel_left] using hshift

theorem actualProjectedPhase_constrainedLine_hasDerivAt {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
        (frozenObliqueRotation * actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j u)).re)
      (frozenObliqueRotation *
        (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
          actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j)).re t := by
  have hh := (actualTotalPhase_constrainedLine_hasDerivAt_any s hs η τ ξ hη hτ hξ θ i j t).const_mul
    frozenObliqueRotation
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hh

end IsingBulk.AnisoF002.Isotropic
