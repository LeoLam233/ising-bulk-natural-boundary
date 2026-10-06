import IsingBulk.Tail.SelectorDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Differential of the actual coupled occupancy shift, with all real bump
derivatives retained. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

 def shiftMap {N : ℕ} (f : SelectorFunctions) (τ : ℝ) (θ : Fin N → ℝ) : Fin N → ℝ :=
  retractionShift τ (fun i => f.p (θ i)) (fun i => f.m (θ i))

 theorem shiftMap_contDiff {N : ℕ} (f : SelectorFunctions) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ContDiff ℝ ∞ (shiftMap (N := N) f τ) := by
  unfold shiftMap retractionShift occupancy
  apply contDiff_pi.mpr
  intro i
  fun_prop

 theorem occupancy_update {N : ℕ} (f : ℝ → ℝ) (θ : Fin N → ℝ) (q : Fin N) (u : ℝ) :
    occupancy (fun i => f (Function.update θ q u i)) =
      f u + ∑ i ∈ Finset.univ.erase q, f (θ i) := by
  unfold occupancy
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

 theorem hasDerivAt_occupancy_update {N : ℕ} (f : ℝ → ℝ) (θ : Fin N → ℝ)
    (q : Fin N) (hf : DifferentiableAt ℝ f (θ q)) :
    HasDerivAt (fun u => occupancy (fun i => f (Function.update θ q u i))) (deriv f (θ q)) (θ q) := by
  simp_rw [occupancy_update]
  exact hf.hasDerivAt.add_const _

 theorem hasDerivAt_shiftMap_coordinate {N : ℕ} (f : SelectorFunctions) (τ : ℝ)
    (θ : Fin N → ℝ) (q i : Fin N)
    (hp : ∀ j, DifferentiableAt ℝ f.p (θ j))
    (hm : ∀ j, DifferentiableAt ℝ f.m (θ j)) :
    HasDerivAt (fun u => shiftMap f τ (Function.update θ q u) i)
      ((if i=q then -2*τ*deriv f.p (θ i)+
          τ*occupancy (fun j => f.p (θ j))/(2*N)*deriv f.m (θ i) else 0)+
        τ/(2*N)*f.m (θ i)*deriv f.p (θ q)) (θ q) := by
  have hP := hasDerivAt_occupancy_update f.p θ q (hp q)
  by_cases hi : i=q
  · subst i
    have h := ((hp q).hasDerivAt.const_mul (-2*τ)).add
      (((hP.const_mul τ).div_const (2*N)).mul (hm q).hasDerivAt)
    simp only [Function.update_eq_self] at h
    convert h using 1
    · funext u
      simp [shiftMap,retractionShift,Function.update_self]
    · simp only [ite_true]
      ring
  · have h := (hasDerivAt_const (θ q) (-2*τ*f.p (θ i))).add
      (((hP.const_mul τ).div_const (2*N)).mul_const (f.m (θ i)))
    convert h using 1
    · funext u
      simp [shiftMap,retractionShift,Function.update_of_ne hi]
    · simp only [hi,ite_false,zero_add]
      ring

 def logContour {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (Real.log r:ℂ)+Complex.I*(θ i:ℂ)+(lam*shiftMap f τ θ i:ℝ)

 theorem logContour_coordinate_deriv {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (q i : Fin N)
    (hp : ∀ j, DifferentiableAt ℝ f.p (θ j))
    (hm : ∀ j, DifferentiableAt ℝ f.m (θ j)) :
    HasDerivAt (fun u => logContour f r τ lam (Function.update θ q u) i)
      (angularJacobian f τ lam θ i q) (θ q) := by
  have hs := (hasDerivAt_shiftMap_coordinate f τ θ q i hp hm).const_mul lam
  have hu : HasDerivAt (fun u : ℝ => Function.update θ q u i)
      (if i=q then 1 else 0) (θ q) := by
    by_cases hi : i=q
    · subst i
      simp only [Function.update_self, ite_true]
      convert hasDerivAt_id (θ q) using 1
      rfl
    · simpa [Function.update_of_ne hi,hi] using hasDerivAt_const (θ q) (θ i)
  have h := ((hasDerivAt_const (θ q) (Real.log r:ℂ)).add (((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt (θ q) hu).const_mul Complex.I)).add ((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt (θ q) hs)
  convert h using 1
  · funext u; rfl
  · unfold angularJacobian retractionJacobian
    by_cases hi : i=q <;> simp only [hi,ite_true,ite_false,Complex.ofRealCLM_apply] <;> push_cast <;> ring

end
end IsingBulk.Tail
