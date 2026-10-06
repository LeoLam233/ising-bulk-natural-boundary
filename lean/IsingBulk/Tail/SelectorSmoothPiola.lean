import IsingBulk.Tail.SelectorPiola
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Schwarz symmetry supplies the local Piola hypotheses for any actual
C² occupancy shift. No conservation identity is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

 def shiftPartial {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (θ : Fin N → ℝ) (k i : Fin N) : ℂ :=
  fderiv ℝ (fun x => h x k) θ (Pi.single i 1)

 def shiftSecond {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (θ : Fin N → ℝ) (i j k : Fin N) : ℂ :=
  fderiv ℝ (fderiv ℝ (fun x => h x k)) θ (Pi.single i 1) (Pi.single j 1)

 theorem smooth_shift_coordinate {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (hh : ContDiff ℝ 2 h) (θ : Fin N → ℝ) (i k : Fin N) :
    HasDerivAt (fun u => h (Function.update θ i u) k) (shiftPartial h θ k i) (θ i) := by
  have hk : DifferentiableAt ℝ (fun x => h x k) θ := by
    exact ((contDiff_apply ℝ ℂ k).comp hh).differentiable (by norm_num) θ
  simpa only [Function.update_eq_self, Function.comp_def, shiftPartial] using
    hk.hasFDerivAt.comp_hasDerivAt_of_eq (θ i) (hasDerivAt_update θ i (θ i)) (by simp)

 theorem smooth_shift_second_symmetric {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (hh : ContDiff ℝ 2 h) (θ : Fin N → ℝ) (i j : Fin N) :
    shiftSecond h θ i j = shiftSecond h θ j i := by
  funext k
  have hk : ContDiff ℝ 2 (fun x => h x k) := (contDiff_apply ℝ ℂ k).comp hh
  exact hk.contDiffAt.isSymmSndFDerivAt (by norm_num) (Pi.single i 1) (Pi.single j 1)

 theorem smooth_shift_partial_coordinate {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (hh : ContDiff ℝ 2 h) (θ : Fin N → ℝ) (i j k : Fin N) :
    HasDerivAt (fun u => shiftPartial h (Function.update θ i u) k j)
      (shiftSecond h θ i j k) (θ i) := by
  have hk : ContDiff ℝ 2 (fun x => h x k) := (contDiff_apply ℝ ℂ k).comp hh
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun x => h x k)) θ :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) θ
  have he := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single j (1:ℝ)) θ)
  have hc := he.comp_hasDerivAt_of_eq (θ i) (hasDerivAt_update θ i (θ i)) (by simp)
  simpa only [Function.update_eq_self, Function.comp_def, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add,
    shiftPartial, shiftSecond] using hc

 def affineShiftJacobian {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (t : ℝ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun k j => (if k=j then Complex.I else 0)+(t:ℂ)*shiftPartial h θ k j

 theorem affineShiftJacobian_parameter {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (t : ℝ) (θ : Fin N → ℝ) (k j : Fin N) :
    HasDerivAt (fun u => affineShiftJacobian h u θ k j) (shiftPartial h θ k j) t := by
  have hc := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (shiftPartial h θ k j)
  simpa only [affineShiftJacobian, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    using hc.const_add (if k=j then Complex.I else 0)

 theorem affineShiftJacobian_coordinate {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℂ)
    (hh : ContDiff ℝ 2 h) (t : ℝ) (θ : Fin N → ℝ) (i k j : Fin N) :
    HasDerivAt (fun u => affineShiftJacobian h t (Function.update θ i u) k j)
      ((t:ℂ)*shiftSecond h θ i j k) (θ i) := by
  exact ((smooth_shift_partial_coordinate h hh θ i j k).const_mul (t:ℂ)).const_add _

 def affineLogMap {N : ℕ} (c : Fin N → ℂ) (h : (Fin N → ℝ) → Fin N → ℂ)
    (t : ℝ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  fun k => c k+Complex.I*(θ k:ℂ)+(t:ℂ)*h θ k

 theorem affineLogMap_parameter {N : ℕ} (c : Fin N → ℂ)
    (h : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ) :
    HasDerivAt (fun u => affineLogMap c h u θ) (h θ) t := by
  apply hasDerivAt_pi.mpr
  intro k
  have hc := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (h θ k)
  simpa only [affineLogMap, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    using hc.const_add (c k+Complex.I*(θ k:ℂ))

 theorem affineLogMap_coordinate {N : ℕ} (c : Fin N → ℂ)
    (h : (Fin N → ℝ) → Fin N → ℂ) (hh : ContDiff ℝ 2 h)
    (t : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun u => affineLogMap c h t (Function.update θ i u))
      (fun k => affineShiftJacobian h t θ k i) (θ i) := by
  apply hasDerivAt_pi.mpr
  intro k
  have hb : HasDerivAt (fun u : ℝ => Complex.I*(Function.update θ i u k:ℝ))
      (if k=i then Complex.I else 0) (θ i) := by
    by_cases hki : k=i
    · subst k
      simpa only [Function.update_self,ite_true, Complex.ofRealCLM_apply,
        Complex.ofReal_one,mul_one] using
        (Complex.ofRealCLM.hasDerivAt (x := θ i)).const_mul Complex.I
    · simpa only [Function.update_of_ne hki,hki,ite_false] using
        hasDerivAt_const (θ i) (Complex.I*(θ k:ℂ))
  exact (hb.const_add (c k)).add ((smooth_shift_coordinate h hh θ i k).const_mul (t:ℂ))

 theorem smooth_affine_homotopy_conservation {N : ℕ} (c : Fin N → ℂ)
    (h : (Fin N → ℝ) → Fin N → ℂ) (hh : ContDiff ℝ 2 h)
    (F : (Fin N → ℂ) → ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hF : DifferentiableAt ℂ F (affineLogMap c h t θ)) :
    deriv (fun u => F (affineLogMap c h u θ)*(affineShiftJacobian h u θ).det) t =
      ∑ i, deriv (fun u => F (affineLogMap c h t (Function.update θ i u))*
        ((affineShiftJacobian h t (Function.update θ i u)).updateCol i
          (h (Function.update θ i u))).det) (θ i) := by
  let L := (fderiv ℂ F (affineLogMap c h t θ)).toLinearMap
  have hFt := hF.hasFDerivAt.restrictScalars ℝ
  apply pointwise_homotopy_conservation (fun u x => F (affineLogMap c h u x))
    (affineShiftJacobian h) h t θ L (fun k i => shiftPartial h θ k i)
    (fun i j k => (t:ℂ)*shiftSecond h θ i j k)
  · intro i j
    funext k
    rw [smooth_shift_second_symmetric h hh θ i j]
  · exact hFt.comp_hasDerivAt t (affineLogMap_parameter c h t θ)
  · intro i
    have h := hFt.comp_hasDerivAt_of_eq (θ i) (affineLogMap_coordinate c h hh t θ i) (by simp)
    convert h using 1 <;> rfl
  · exact affineShiftJacobian_parameter h t θ
  · exact affineShiftJacobian_coordinate h hh t θ
  · exact smooth_shift_coordinate h hh θ

end
end IsingBulk.Tail
