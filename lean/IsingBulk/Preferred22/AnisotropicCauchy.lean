import IsingBulk.Preferred22.AnalyticCauchyBounds
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Actual mixed parameter/coordinate Cauchy bounds. The parameter scale
and the q scale remain separate in the derivative directions. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The two independent scalar rescalings as an actual invertible linear map. -/
def complexAnisotropicScale (a b : ℂ) (ha : a≠0) (hb : b≠0) :
    (ℂ × E) ≃L[ℂ] (ℂ × E) where
  toFun z := (a*z.1,b • z.2)
  invFun z := (a⁻¹*z.1,b⁻¹ • z.2)
  left_inv z := by simp [ha,hb,smul_smul]
  right_inv z := by simp [ha,hb,smul_smul]
  map_add' z w := by simp [mul_add,smul_add]
  map_smul' c z := by simp [smul_smul,mul_comm,mul_left_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [CompleteSpace F] in
/-- Exact change of all derivative directions under anisotropic scaling.
Because the scaling is invertible, this identity also respects Lean's
totalized Fréchet derivative outside differentiability points. -/
theorem complexAnisotropicScale_iteratedFDeriv (f : ℂ × E → F) (x : ℂ × E)
    (a b : ℂ) (ha : a≠0) (hb : b≠0) (n : ℕ) (v : Fin n → ℂ × E) :
    iteratedFDeriv ℂ n f x v =
      iteratedFDeriv ℂ n (fun z => f (x+complexAnisotropicScale a b ha hb z)) 0
        (fun k => (complexAnisotropicScale a b ha hb).symm (v k)) := by
  let L : (ℂ × E) ≃L[ℂ] (ℂ × E) := complexAnisotropicScale a b ha hb
  have hh := L.iteratedFDerivWithin_comp_right (fun z => f (x+z))
    (s:=Set.univ) uniqueDiffOn_univ (x:=0) (by simp) n
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ,map_zero,
    iteratedFDeriv_comp_add_left,add_zero] at hh
  have hh' := congrArg (fun T => T (fun k => L.symm (v k))) hh
  simpa only [L,Function.comp_def,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hh'.symm

/-- The exact anisotropic norm bound for actual mixed Fréchet jets. A
parameter direction costs 1/a; a q direction costs 1/(a*d). -/
theorem anisotropic_cauchy_mixed_bound (f : ℂ × E → F) (x : ℂ × E)
    (a d M : ℝ) (ha : 0<a) (hd : 0<d)
    (hf : AnalyticOnNhd ℂ (fun z : ℂ × E => f (x.1+(a:ℂ)*z.1,x.2+((a*d:ℝ):ℂ) • z.2))
      (ball 0 1))
    (hM : ∀ z∈ball (0:ℂ × E) 1,
      ‖f (x.1+(a:ℂ)*z.1,x.2+((a*d:ℝ):ℂ) • z.2)‖≤M)
    (n : ℕ) (v : Fin n → ℂ × E) :
    ‖iteratedFDeriv ℂ n f x v‖≤
      cauchyJetConstant n*M/a^n * ∏ k, max ‖(v k).1‖ (‖(v k).2‖/d) := by
  have haC : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hadC : ((a*d:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (mul_pos ha hd).ne'
  let L := complexAnisotropicScale (E:=E) (a:ℂ) ((a*d:ℝ):ℂ) haC hadC
  let H : ℂ × E → F := fun z => f (x+L z)
  have hH : AnalyticOnNhd ℂ H (ball 0 1) := hf
  have hHb : ∀ z∈ball (0:ℂ × E) 1, ‖H z‖≤M := hM
  have hjet := analytic_iteratedFDeriv_center_bound H 0 1 M (by norm_num) hH hHb n
  simp only [one_pow,div_one] at hjet
  have hdir (k : Fin n) : ‖L.symm (v k)‖=
      a⁻¹*max ‖(v k).1‖ (‖(v k).2‖/d) := by
    change max ‖(a:ℂ)⁻¹*(v k).1‖ ‖((a*d:ℝ):ℂ)⁻¹ • (v k).2‖ = _
    simp only [norm_mul,norm_inv,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ha,abs_of_pos hd]
    rw [mul_inv_rev]
    rw [show d⁻¹*a⁻¹*‖(v k).2‖=a⁻¹*(‖(v k).2‖/d) by ring]
    exact (mul_max_of_nonneg _ _ (inv_nonneg.mpr ha.le)).symm
  rw [complexAnisotropicScale_iteratedFDeriv f x (a:ℂ) ((a*d:ℝ):ℂ) haC hadC]
  change ‖iteratedFDeriv ℂ n H 0 (fun k => L.symm (v k))‖≤_
  calc
    _ ≤ ‖iteratedFDeriv ℂ n H 0‖ * ∏ k, ‖L.symm (v k)‖ :=
      (iteratedFDeriv ℂ n H 0).le_opNorm _
    _ ≤ (cauchyJetConstant n*M) * ∏ k, ‖L.symm (v k)‖ :=
      mul_le_mul_of_nonneg_right hjet (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by
      simp_rw [hdir]
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      rw [inv_pow]
      ring

end
end IsingBulk.Preferred22
