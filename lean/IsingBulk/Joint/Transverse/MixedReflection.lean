import IsingBulk.Joint.Transverse.AnalyticReflection
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Exact all-order mixed Fréchet derivative reflection. Unlike a scalar
jet assertion, this transports the full continuous multilinear derivative
and therefore its operator norm, without a factorial or dimension loss. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [StarAddMonoid F] [StarModule ℂ F] [NormedStarGroup F]

@[simp] theorem reflectedMultilinear_add {n : ℕ} (p q : E [×n]→L[ℂ] F) :
    reflectedMultilinear (p+q)=reflectedMultilinear p+reflectedMultilinear q := by
  ext v
  change star ((p+q) (star v))=star (p (star v))+star (q (star v))
  simp only [add_apply,star_add]

@[simp] theorem reflectedMultilinear_smul {n : ℕ} (a : ℂ) (p : E [×n]→L[ℂ] F) :
    reflectedMultilinear (a • p)=star a • reflectedMultilinear p := by
  ext v
  change star ((a • p) (star v))=star a • star (p (star v))
  simp only [smul_apply,star_smul]

@[simp] theorem reflectedMultilinear_twice {n : ℕ} (p : E [×n]→L[ℂ] F) :
    reflectedMultilinear (reflectedMultilinear p)=p := by
  ext v
  change star (star (p (star (star v))))=p v
  simp only [star_star]

theorem reflectedMultilinear_norm {n : ℕ} (p : E [×n]→L[ℂ] F) :
    ‖reflectedMultilinear p‖=‖p‖ := by
  apply le_antisymm (reflectedMultilinear_norm_le p)
  simpa only [reflectedMultilinear_twice] using reflectedMultilinear_norm_le (reflectedMultilinear p)

/-- The coefficient reflection is an actual continuous conjugate-linear map. -/
def reflectedMultilinearL (n : ℕ) :
    (E [×n]→L[ℂ] F) →SL[starRingEnd ℂ] (E [×n]→L[ℂ] F) :=
  ({ toFun := reflectedMultilinear
     map_add' := reflectedMultilinear_add
     map_smul' := reflectedMultilinear_smul } :
    (E [×n]→L[ℂ] F) →ₛₗ[starRingEnd ℂ] (E [×n]→L[ℂ] F)).mkContinuous 1
      (fun p => by
        change ‖reflectedMultilinear p‖≤1*‖p‖
        simpa only [one_mul] using reflectedMultilinear_norm_le p)

@[simp] theorem reflectedMultilinearL_apply (n : ℕ) (p : E [×n]→L[ℂ] F) :
    reflectedMultilinearL n p=reflectedMultilinear p := rfl

/-- Reflection of every mixed complex derivative, assuming exactly the
finite differentiability order being used. Joint analyticity is not required. -/
theorem iteratedFDeriv_star_star (n : ℕ) {f : E→F} {x : E}
    (hf : ContDiffAt ℂ n f x) :
    iteratedFDeriv ℂ n (fun y=>star (f (star y))) (star x)=
      reflectedMultilinear (iteratedFDeriv ℂ n f x) := by
  induction n generalizing x with
  | zero =>
    ext v
    change star (f (star (star x)))=star (iteratedFDeriv ℂ 0 f x (star v))
    simp only [star_star,iteratedFDeriv_zero_apply]
  | succ n ih =>
    have hs : Tendsto (star : E→E) (𝓝 (star x)) (𝓝 x) := by
      simpa only [star_star] using continuous_star.tendsto (star x)
    have he : iteratedFDeriv ℂ n (fun y=>star (f (star y))) =ᶠ[𝓝 (star x)]
        (fun y=>reflectedMultilinear (iteratedFDeriv ℂ n f (star y))) := by
      filter_upwards [hs.eventually (hf.eventually (by simp))] with y hy
      simpa only [star_star] using ih (hy.of_le (by simp))
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) x :=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hd' : HasFDerivAt (iteratedFDeriv ℂ n f) (fderiv ℂ (iteratedFDeriv ℂ n f) x)
        ((starL ℂ : E ≃L⋆[ℂ] E) (star x)) := by
      simpa only [starL_apply,star_star] using hd.hasFDerivAt
    have href := hd'.comp_semilinear (reflectedMultilinearL n) (starL ℂ).toContinuousLinearMap
    ext v
    rw [iteratedFDeriv_succ_apply_left,he.fderiv_eq]
    change (fderiv ℂ (reflectedMultilinearL n ∘ iteratedFDeriv ℂ n f ∘ (starL ℂ).toContinuousLinearMap)
      (star x)) (v 0) (Fin.tail v)=_
    rw [href.fderiv]
    change star ((fderiv ℂ (iteratedFDeriv ℂ n f) x) (star (v 0)) (star (Fin.tail v)))=
      star (iteratedFDeriv ℂ (n+1) f x (star v))
    rw [iteratedFDeriv_succ_apply_left]
    rfl

/-- Exact mixed operator norm invariance, so summable all-particle majorants
transfer with their original constants and common radii. -/
theorem norm_iteratedFDeriv_star_star (n : ℕ) {f : E→F} {x : E}
    (hf : ContDiffAt ℂ n f x) :
    ‖iteratedFDeriv ℂ n (fun y=>star (f (star y))) (star x)‖=
      ‖iteratedFDeriv ℂ n f x‖ := by
  rw [iteratedFDeriv_star_star n hf,reflectedMultilinear_norm]

end
end IsingBulk.Joint.Transverse
