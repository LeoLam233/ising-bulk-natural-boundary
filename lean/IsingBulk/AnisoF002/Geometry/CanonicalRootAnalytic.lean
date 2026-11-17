import IsingBulk.AnisoF002.Geometry.CanonicalRootAlgebra
import IsingBulk.AnisoF002.Geometry.EndpointBoundary
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Joint analytic neighborhoods of the actual spectral root

F002 `lem:canonicalroot`: an inverse-function construction for the full
unsquared polynomial, without dividing by the spectral coefficient S.
It therefore continues the canonical root through S=0. The local branch
is constructed here, not supplied as an additional physical hypothesis.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Filter
open scoped Topology

def quadraticCoordinateMap (x : (ℂ × ℂ) × ℂ) : (ℂ × ℂ) × ℂ :=
  (x.1, x.1.1 * x.2 ^ 2 - 2 * x.1.2 * x.2 + x.1.1)

def quadraticCoordinateDerivative (S C r : ℂ) :
    ((ℂ × ℂ) × ℂ) →L[ℂ] ((ℂ × ℂ) × ℂ) :=
  (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ).prod
    ((r ^ 2 + 1) • ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
        (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)) -
      (2 * r) • ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)) +
      (2 * S * r - 2 * C) • (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ))

theorem quadraticCoordinateMap_analyticAt (x : (ℂ × ℂ) × ℂ) :
    AnalyticAt ℂ quadraticCoordinateMap x := by
  unfold quadraticCoordinateMap
  have hf : AnalyticAt ℂ (fun a : (ℂ × ℂ) × ℂ => a.1) x := analyticAt_fst
  have hs : AnalyticAt ℂ (fun a : (ℂ × ℂ) × ℂ => a.1.1) x := analyticAt_fst.comp hf
  have hc : AnalyticAt ℂ (fun a : (ℂ × ℂ) × ℂ => a.1.2) x := analyticAt_snd.comp hf
  have hu : AnalyticAt ℂ (fun a : (ℂ × ℂ) × ℂ => a.2) x := analyticAt_snd
  exact hf.prod (((hs.mul (hu.pow 2)).sub ((analyticAt_const.mul hc).mul hu)).add hs)

theorem quadraticCoordinateDerivative_apply (S C r : ℂ) (a : (ℂ × ℂ) × ℂ) :
    quadraticCoordinateDerivative S C r a =
      (a.1, (r ^ 2 + 1) * a.1.1 - 2 * r * a.1.2 + (2 * S * r - 2 * C) * a.2) := by
  simp [quadraticCoordinateDerivative]

theorem quadraticCoordinateMap_hasStrictFDerivAt (S C r : ℂ) :
    HasStrictFDerivAt quadraticCoordinateMap (quadraticCoordinateDerivative S C r) ((S, C), r) := by
  let f : ((ℂ × ℂ) × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ
  let s : ((ℂ × ℂ) × ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.fst ℂ ℂ ℂ).comp f
  let c : ((ℂ × ℂ) × ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.snd ℂ ℂ ℂ).comp f
  let u : ((ℂ × ℂ) × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ
  have hs : HasStrictFDerivAt (fun x : (ℂ × ℂ) × ℂ => x.1.1) s ((S, C), r) :=
    s.hasStrictFDerivAt
  have hc : HasStrictFDerivAt (fun x : (ℂ × ℂ) × ℂ => x.1.2) c ((S, C), r) :=
    c.hasStrictFDerivAt
  have hu : HasStrictFDerivAt (fun x : (ℂ × ℂ) × ℂ => x.2) u ((S, C), r) :=
    u.hasStrictFDerivAt
  have hf : HasStrictFDerivAt (fun x : (ℂ × ℂ) × ℂ => x.1) f ((S, C), r) :=
    f.hasStrictFDerivAt
  convert hf.prodMk (((hs.mul (hu.mul hu)).sub ((hc.const_mul 2).mul hu)).add hs) using 1
  · funext x
    simp [quadraticCoordinateMap, pow_two]
  · apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext
    · rfl
    · simp [quadraticCoordinateDerivative, f, s, c, u, pow_two]
      ring

theorem quadraticCoordinateDerivative_bijective (S C r : ℂ)
    (hD : 2 * S * r - 2 * C ≠ 0) :
    Function.Bijective (quadraticCoordinateDerivative S C r) := by
  constructor
  · intro a b hab
    have hp := congrArg Prod.fst hab
    have hv := congrArg Prod.snd hab
    simp only [quadraticCoordinateDerivative_apply] at hp hv
    apply Prod.ext hp
    have hz : (2 * S * r - 2 * C) * (a.2 - b.2) = 0 := by
      rw [hp] at hv
      linear_combination hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hD)
  · intro b
    refine ⟨(b.1, (b.2 - (r ^ 2 + 1) * b.1.1 + 2 * r * b.1.2) /
      (2 * S * r - 2 * C)), ?_⟩
    rw [quadraticCoordinateDerivative_apply]
    apply Prod.ext
    · rfl
    · dsimp
      rw [mul_div_cancel₀]
      · ring
      · exact hD

theorem exists_joint_analytic_quadratic_root (S C r : ℂ)
    (hp : S * r ^ 2 - 2 * C * r + S = 0)
    (hD : 2 * S * r - 2 * C ≠ 0) (hn : ‖r‖ < 1) :
    ∃ R : ℂ × ℂ → ℂ,
      AnalyticAt ℂ R (S, C) ∧ R (S, C) = r ∧
      ∀ᶠ a in 𝓝 (S, C), a.1 * R a ^ 2 - 2 * a.2 * R a + a.1 = 0 ∧ ‖R a‖ < 1 := by
  let e : ((ℂ × ℂ) × ℂ) ≃L[ℂ] ((ℂ × ℂ) × ℂ) :=
    (LinearEquiv.ofBijective (quadraticCoordinateDerivative S C r).toLinearMap
      (quadraticCoordinateDerivative_bijective S C r hD)).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt quadraticCoordinateMap
      (e : ((ℂ × ℂ) × ℂ) →L[ℂ] ((ℂ × ℂ) × ℂ)) ((S, C), r) :=
    quadraticCoordinateMap_hasStrictFDerivAt S C r
  let H := hs.toOpenPartialHomeomorph quadraticCoordinateMap
  have hm : ((S, C), r) ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hvalue : quadraticCoordinateMap ((S, C), r) = ((S, C), 0) := by
    exact Prod.ext rfl hp
  have hi : AnalyticAt ℂ H.symm ((S, C), 0) := by
    rw [← hvalue]
    apply H.analyticAt_symm' hm (quadraticCoordinateMap_analyticAt _) hs.hasFDerivAt.fderiv
  let R : ℂ × ℂ → ℂ := fun a => (H.symm (a, 0)).2
  have hinj : AnalyticAt ℂ (fun a : ℂ × ℂ => (a, (0 : ℂ))) (S, C) :=
    analyticAt_id.prod analyticAt_const
  have ha : AnalyticAt ℂ R (S, C) := analyticAt_snd.comp (hi.comp_of_eq hinj rfl)
  have hv : R (S, C) = r := by
    change (H.symm ((S, C), 0)).2 = r
    rw [← hvalue]
    exact congrArg Prod.snd (H.left_inv hm)
  refine ⟨R, ha, hv, ?_⟩
  have he : ∀ᶠ a in 𝓝 (S, C), quadraticCoordinateMap (H.symm (a, 0)) = (a, 0) := by
    have h : ∀ᶠ y in 𝓝 (quadraticCoordinateMap ((S, C), r)),
        quadraticCoordinateMap (H.symm y) = y := H.eventually_right_inverse' hm
    rw [hvalue] at h
    exact (continuousAt_id.prodMk continuousAt_const).eventually h
  have hnorm : ∀ᶠ a in 𝓝 (S, C), ‖R a‖ < 1 :=
    ha.continuousAt.norm.eventually (gt_mem_nhds (by simpa [hv] using hn))
  filter_upwards [he, hnorm] with a hea hna
  have hcoef := congrArg Prod.fst hea
  have hpoly := congrArg Prod.snd hea
  change (H.symm (a, 0)).1 = a at hcoef
  change (H.symm (a, 0)).1.1 * R a ^ 2 -
    2 * (H.symm (a, 0)).1.2 * R a + (H.symm (a, 0)).1.1 = 0 at hpoly
  rw [hcoef] at hpoly
  exact ⟨hpoly, hna⟩

def spectralCoefficientsF002 (lam : ℝ) (a : ℂ × ℂ) : ℂ × ℂ :=
  (spectralS a.1, spectralA lam a.1 - spectralT lam a.1 * Complex.cos a.2)

theorem spectralCoefficientsF002_analyticAt (lam : ℝ) (a : ℂ × ℂ) :
    AnalyticAt ℂ (spectralCoefficientsF002 lam) a := by
  delta spectralCoefficientsF002 spectralS spectralA spectralT
  exact (Complex.analyticAt_sinh.comp analyticAt_fst).prod
    (((Complex.analyticAt_cosh.comp analyticAt_fst).mul
      (Complex.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_fst))).sub
      ((Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_fst)).mul
        (Complex.analyticAt_cos.comp analyticAt_snd)))

/-- A joint complex parameter/angle branch of the genuine interior root,
including the removable zero-S points. -/
theorem exists_joint_analytic_spectral_root {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    ∃ R : ℂ × ℂ → ℂ,
      AnalyticAt ℂ R (z, (q : ℂ)) ∧
      R (z, (q : ℂ)) = spectralSmallRootF002 lam z q ∧
      ∀ᶠ a in 𝓝 (z, (q : ℂ)),
        spectralS a.1 * R a ^ 2 -
          2 * (spectralA lam a.1 - spectralT lam a.1 * Complex.cos a.2) * R a +
          spectralS a.1 = 0 ∧ ‖R a‖ < 1 := by
  have hs := spectralSmallRootF002_spec q hz
  obtain ⟨R, hR, hval, he⟩ := exists_joint_analytic_quadratic_root
    (spectralS z) (spectralA lam z - spectralT lam z * (Real.cos q : ℂ))
    (spectralSmallRootF002 lam z q) hs.1 (spectralSmallRootF002_simple q hz) hs.2
  have hv : spectralCoefficientsF002 lam (z, (q : ℂ)) =
      (spectralS z, spectralA lam z - spectralT lam z * (Real.cos q : ℂ)) := by
    simp only [spectralCoefficientsF002, ← Complex.ofReal_cos]
  refine ⟨R ∘ spectralCoefficientsF002 lam, ?_, ?_, ?_⟩
  · apply AnalyticAt.comp _ (spectralCoefficientsF002_analyticAt lam _)
    rwa [hv]
  · simpa only [Function.comp_apply, hv] using hval
  · have ha := (spectralCoefficientsF002_analyticAt lam (z, (q : ℂ))).continuousAt
    have hat := ha.tendsto
    rw [hv] at hat
    exact hat.eventually he

end
end IsingBulk.AnisoF002.Geometry
