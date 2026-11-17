import IsingBulk.AnisoF002.Isotropic.RegularInverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual joint analytic inverse of the isotropic dispersion

The map `(w, φ) ↦ (cos w + cos φ, w + φ)` supplies the local inverse
used in frozen F002 Lemma 7.3 and `eq:iso-regular-factors`.  Its derivative
is invertible whenever `sin φ - sin w ≠ 0`, including `φ = 0` at the
lower branch.  This file constructs the joint analytic inverse; it does
not assume that an unspecified inverse has already been supplied.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter

/-- The actual dispersion and regular-coordinate map. -/
def dispersionCoordinateMap (z : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.cos z.1 + Complex.cos z.2, z.1 + z.2)

/-- Its complete two-variable derivative. -/
def dispersionCoordinateDerivative (w φ : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((-Complex.sin w) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (-Complex.sin φ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    (ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem dispersionCoordinateMap_analyticAt (z : ℂ × ℂ) :
    AnalyticAt ℂ dispersionCoordinateMap z := by
  exact ((Complex.analyticAt_cos.comp analyticAt_fst).add
    (Complex.analyticAt_cos.comp analyticAt_snd)).prod
      (analyticAt_fst.add analyticAt_snd)

theorem dispersionCoordinateMap_hasStrictFDerivAt (w φ : ℂ) :
    HasStrictFDerivAt dispersionCoordinateMap
      (dispersionCoordinateDerivative w φ) (w, φ) := by
  have hfst : HasStrictFDerivAt (fun z : ℂ × ℂ => z.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) (w, φ) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun z : ℂ × ℂ => z.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) (w, φ) := hasStrictFDerivAt_snd
  exact (hfst.ccos.add hsnd.ccos).prodMk (hfst.add hsnd)

theorem dispersionCoordinateDerivative_apply (w φ : ℂ) (a : ℂ × ℂ) :
    dispersionCoordinateDerivative w φ a =
      (-Complex.sin w * a.1 - Complex.sin φ * a.2, a.1 + a.2) := by
  simp [dispersionCoordinateDerivative, sub_eq_add_neg]

/-- The determinant condition is the unsquared regular inverse denominator. -/
theorem dispersionCoordinateDerivative_bijective (w φ : ℂ)
    (hden : Complex.sin φ - Complex.sin w ≠ 0) :
    Function.Bijective (dispersionCoordinateDerivative w φ) := by
  constructor
  · intro a b hab
    have h₁ := congrArg Prod.fst hab
    have h₂ := congrArg Prod.snd hab
    simp only [dispersionCoordinateDerivative_apply] at h₁ h₂
    have hA : (Complex.sin φ - Complex.sin w) * (a.1 - b.1) = 0 := by
      linear_combination h₁ + Complex.sin φ * h₂
    have hfst : a.1 = b.1 := sub_eq_zero.mp ((mul_eq_zero.mp hA).resolve_left hden)
    apply Prod.ext hfst
    linear_combination h₂ - (hfst)
  · intro b
    refine ⟨((b.1 + Complex.sin φ * b.2) / (Complex.sin φ - Complex.sin w),
      (-b.1 - Complex.sin w * b.2) / (Complex.sin φ - Complex.sin w)), ?_⟩
    rw [dispersionCoordinateDerivative_apply]
    apply Prod.ext <;> dsimp <;> field_simp [hden] <;> ring

/-- A genuine joint analytic inverse, with its value and original dispersion
identity on a neighborhood in both `S` and `v`. -/
theorem exists_joint_analytic_inverse (w φ : ℂ)
    (hden : Complex.sin φ - Complex.sin w ≠ 0) :
    ∃ U : (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ U (Complex.cos w + Complex.cos φ, w + φ) ∧
      U (Complex.cos w + Complex.cos φ, w + φ) = w ∧
      ∀ᶠ q in 𝓝 (Complex.cos w + Complex.cos φ, w + φ),
        Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1 := by
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (dispersionCoordinateDerivative w φ).toLinearMap
      (dispersionCoordinateDerivative_bijective w φ hden)).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt dispersionCoordinateMap
      (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (w, φ) :=
    dispersionCoordinateMap_hasStrictFDerivAt w φ
  let H := hs.toOpenPartialHomeomorph dispersionCoordinateMap
  have hm : (w, φ) ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hi : AnalyticAt ℂ H.symm (dispersionCoordinateMap (w, φ)) := by
    apply H.analyticAt_symm' hm
    · exact dispersionCoordinateMap_analyticAt (w, φ)
    · exact hs.hasFDerivAt.fderiv
  refine ⟨fun q => (H.symm q).1, analyticAt_fst.comp hi, ?_, ?_⟩
  · exact congrArg Prod.fst (H.left_inv hm)
  · have he : ∀ᶠ q in 𝓝 (dispersionCoordinateMap (w, φ)),
        dispersionCoordinateMap (H.symm q) = q :=
      H.eventually_right_inverse' hm
    filter_upwards [he] with q hq
    have h₁ := congrArg Prod.fst hq
    have h₂ := congrArg Prod.snd hq
    change Complex.cos (H.symm q).1 + Complex.cos (H.symm q).2 = q.1 at h₁
    change (H.symm q).1 + (H.symm q).2 = q.2 at h₂
    have hφ : q.2 - (H.symm q).1 = (H.symm q).2 := by linear_combination -h₂
    simpa only [hφ] using h₁

/-- The lower square-root branch is regular in the joint `(S,v)` coordinates. -/
theorem exists_joint_analytic_inverse_at_branch (w : ℂ)
    (hw : Complex.sin w ≠ 0) :
    ∃ U : (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ U (Complex.cos w + 1, w) ∧
      U (Complex.cos w + 1, w) = w ∧
      ∀ᶠ q in 𝓝 (Complex.cos w + 1, w),
        Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1 := by
  simpa only [Complex.sin_zero, zero_sub, ne_eq, neg_eq_zero,
    Complex.cos_zero, add_zero] using exists_joint_analytic_inverse w 0 (by simpa using hw)

/-- The apparent one-body singularity has an actual joint analytic extension
on every inverse neighborhood with the regular denominator separated. -/
theorem joint_regularOneBody_analyticAt (U : (ℂ × ℂ) → ℂ) (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ U q)
    (hden : Complex.sin (q.2 - U q) - Complex.sin (U q) ≠ 0) :
    AnalyticAt ℂ (fun z => regularOneBody (U z) (z.2 - U z)) q := by
  unfold regularOneBody
  exact analyticAt_const.div
    ((Complex.analyticAt_sin.comp (analyticAt_snd.sub hU)).sub
      (Complex.analyticAt_sin.comp hU)) hden

/-- The jointly analytic inverse supplies each fixed-parameter coordinate
derivative of the exact physical dispersion. -/
theorem joint_inverse_coordinate_derivative
    (U : (ℂ × ℂ) → ℂ) (S v : ℂ) (hU : AnalyticAt ℂ U (S, v))
    (hdisp : ∀ᶠ q in 𝓝 (S, v),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hden : Complex.sin (v - U (S, v)) - Complex.sin (U (S, v)) ≠ 0) :
    HasDerivAt (fun z => U (S, z))
      (Complex.sin (v - U (S, v)) /
        (Complex.sin (v - U (S, v)) - Complex.sin (U (S, v)))) v := by
  have ha : AnalyticAt ℂ (fun z => U (S, z)) v :=
    hU.comp (analyticAt_const.prod analyticAt_id)
  have hd := ha.differentiableAt.hasDerivAt
  have he : (fun z => Complex.cos (U (S, z)) + Complex.cos (z - U (S, z)))
      =ᶠ[𝓝 v] (fun _ => S) := by
    exact (continuousAt_const.prodMk continuousAt_id).eventually hdisp
  have heq := inverse_coordinate_derivative (fun z => U (S, z)) S v _ hd he hden
  simpa only [heq] using hd

/-- Joint analyticity likewise supplies the physical parameter derivative. -/
theorem joint_inverse_parameter_derivative
    (U : (ℂ × ℂ) → ℂ) (S v : ℂ) (hU : AnalyticAt ℂ U (S, v))
    (hdisp : ∀ᶠ q in 𝓝 (S, v),
      Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1)
    (hden : Complex.sin (v - U (S, v)) - Complex.sin (U (S, v)) ≠ 0) :
    HasDerivAt (fun z => U (z, v))
      (1 / (Complex.sin (v - U (S, v)) - Complex.sin (U (S, v)))) S := by
  have ha : AnalyticAt ℂ (fun z => U (z, v)) S :=
    hU.comp (f := fun z : ℂ => (z, v)) (analyticAt_id.prod analyticAt_const)
  have hd := ha.differentiableAt.hasDerivAt
  have he : (fun z => Complex.cos (U (z, v)) + Complex.cos (v - U (z, v)))
      =ᶠ[𝓝 S] id := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually hdisp
  have heq := inverse_parameter_derivative (fun z => U (z, v)) S v _ hd he hden
  simpa only [heq] using hd

end IsingBulk.AnisoF002.Isotropic
