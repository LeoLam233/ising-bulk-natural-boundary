import IsingBulk.Joint.Geometry.ExactSpectrum
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Analytic.Inverse

namespace IsingBulk.Joint
noncomputable section
open ContinuousLinearMap

/-- Explicit continuous complex-linear differential of C=A/S. -/
def transferCDerivative (K : Coupling) : Coupling →L[ℂ] ℂ :=
  (-(Complex.cosh K.2) / S K^2) • fst ℂ ℂ ℂ +
  (Complex.cosh K.1 * T K / S K) • snd ℂ ℂ ℂ

/-- Explicit continuous complex-linear differential of B=T/S. -/
def transferBDerivative (K : Coupling) : Coupling →L[ℂ] ℂ :=
  (-(T K * Complex.cosh K.1) / S K^2) • fst ℂ ℂ ℂ +
  (Complex.cosh K.2 / S K) • snd ℂ ℂ ℂ

def transferDerivative (K : Coupling) : Coupling →L[ℂ] Coupling :=
  (transferCDerivative K).prod (transferBDerivative K)

theorem hasStrictFDerivAt_transferC {K : Coupling} (hS : S K≠0) :
    HasStrictFDerivAt transferC (transferCDerivative K) K := by
  have hz : HasStrictFDerivAt (fun J : Coupling => J.1) (fst ℂ ℂ ℂ) K := hasStrictFDerivAt_fst
  have hw : HasStrictFDerivAt (fun J : Coupling => J.2) (snd ℂ ℂ ℂ) K := hasStrictFDerivAt_snd
  have hi := (hasStrictDerivAt_inv hS).comp_hasStrictFDerivAt K hz.csinh
  have h := (hz.ccosh.fun_mul hw.ccosh).fun_mul hi
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [transferCDerivative]
  change -Complex.cosh K.2 / S K ^ 2 * v.1 +
    (Complex.cosh K.1 * T K / S K) * v.2 = _
  simp [smul_eq_mul]
  have hh := Complex.cosh_sq_sub_sinh_sq K.1
  dsimp [S,T,A] at *
  field_simp
  linear_combination (Complex.cosh K.2)*v.1*hh

theorem hasStrictFDerivAt_transferB {K : Coupling} (hS : S K≠0) :
    HasStrictFDerivAt transferB (transferBDerivative K) K := by
  have hz : HasStrictFDerivAt (fun J : Coupling => J.1) (fst ℂ ℂ ℂ) K := hasStrictFDerivAt_fst
  have hw : HasStrictFDerivAt (fun J : Coupling => J.2) (snd ℂ ℂ ℂ) K := hasStrictFDerivAt_snd
  have hi := (hasStrictDerivAt_inv hS).comp_hasStrictFDerivAt K hz.csinh
  have h := hw.csinh.fun_mul hi
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [transferBDerivative,smul_eq_mul]
  dsimp [S,T]
  field_simp

theorem hasStrictFDerivAt_transferChart {K : Coupling} (hS : S K≠0) :
    HasStrictFDerivAt transferChart (transferDerivative K) K :=
  (hasStrictFDerivAt_transferC hS).prodMk (hasStrictFDerivAt_transferB hS)

/-- This determinant is defined from the actual Fréchet derivative, not a formal Jacobian. -/
def transferJacobian (K : Coupling) : ℂ :=
  (fderiv ℂ transferChart K (1,0)).1 * (fderiv ℂ transferChart K (0,1)).2 -
  (fderiv ℂ transferChart K (0,1)).1 * (fderiv ℂ transferChart K (1,0)).2

/-- JOINT (2.21) for the actual independent complex derivative. -/
theorem transferJacobian_eq {K : Coupling} (hS : S K≠0) :
    transferJacobian K = (p K^2-1)/S K^3 := by
  rw [transferJacobian,(hasStrictFDerivAt_transferChart hS).hasFDerivAt.fderiv]
  simp [transferDerivative,transferCDerivative,transferBDerivative,smul_eq_mul]
  have hx := Complex.cosh_sq_sub_sinh_sq K.1
  have hw := Complex.cosh_sq_sub_sinh_sq K.2
  dsimp [S,T,p] at *
  field_simp
  linear_combination (Complex.sinh K.2)^2*hx-hw

theorem transferJacobian_ne_zero {K : Coupling} (hS : S K≠0) (hp : p K^2≠1) :
    transferJacobian K≠0 := by
  rw [transferJacobian_eq hS]
  exact div_ne_zero (sub_ne_zero.mpr hp) (pow_ne_zero _ hS)

private theorem twoByTwo_bijective (f : Coupling →L[ℂ] Coupling)
    (hd : (f (1,0)).1*(f (0,1)).2-(f (0,1)).1*(f (1,0)).2≠0) : Function.Bijective f := by
  let a := (f (1,0)).1
  let b := (f (0,1)).1
  let c := (f (1,0)).2
  let d := (f (0,1)).2
  change a*d-b*c≠0 at hd
  have he (v : Coupling) : f v=(a*v.1+b*v.2,c*v.1+d*v.2) := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    calc
      f v = f (v.1 • (1,0)+v.2 • (0,1)) := congrArg f hv
      _ = _ := by
        rw [map_add,map_smul,map_smul]
        ext <;> simp [a,b,c,d,smul_eq_mul,mul_comm]
  constructor
  · intro v w hv
    have h1 := congrArg Prod.fst hv
    have h2 := congrArg Prod.snd hv
    rw [he,he] at h1 h2
    have he1 : (a*d-b*c)*(v.1-w.1)=0 := by linear_combination d*h1-b*h2
    have he2 : (a*d-b*c)*(v.2-w.2)=0 := by linear_combination a*h2-c*h1
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp he1).resolve_left hd))
      (sub_eq_zero.mp ((mul_eq_zero.mp he2).resolve_left hd))
  · intro v
    refine ⟨((d*v.1-b*v.2)/(a*d-b*c),(a*v.2-c*v.1)/(a*d-b*c)),?_⟩
    rw [he]
    apply Prod.ext <;> dsimp
    · rw [← mul_div_assoc,← mul_div_assoc,← add_div,div_eq_iff hd]
      ring
    · rw [← mul_div_assoc,← mul_div_assoc,← add_div,div_eq_iff hd]
      ring

theorem transferDerivative_bijective {K : Coupling} (hS : S K≠0) (hp : p K^2≠1) :
    Function.Bijective (transferDerivative K) := by
  apply twoByTwo_bijective
  have h := transferJacobian_ne_zero hS hp
  simpa only [transferJacobian,(hasStrictFDerivAt_transferChart hS).hasFDerivAt.fderiv] using h

/-- Local coordinate inverse constructed by the complex inverse-function theorem. -/
theorem exists_transfer_localHomeomorph {K : Coupling} (hS : S K≠0) (hp : p K^2≠1) :
    ∃ e : OpenPartialHomeomorph Coupling Coupling,
      K∈e.source ∧ (e : Coupling → Coupling)=transferChart ∧
      DifferentiableAt ℂ e.symm (transferChart K) := by
  let d : Coupling ≃L[ℂ] Coupling := ContinuousLinearEquiv.ofBijective
    (transferDerivative K) (LinearMap.ker_eq_bot.mpr (transferDerivative_bijective hS hp).1)
    (LinearMap.range_eq_top.mpr (transferDerivative_bijective hS hp).2)
  have hd : HasStrictFDerivAt transferChart (d : Coupling →L[ℂ] Coupling) K :=
    hasStrictFDerivAt_transferChart hS
  refine ⟨hd.toOpenPartialHomeomorph transferChart,hd.mem_toOpenPartialHomeomorph_source,
    hd.toOpenPartialHomeomorph_coe,?_⟩
  exact hd.to_localInverse.hasFDerivAt.differentiableAt

theorem transferC_analyticAt {K : Coupling} (hS : S K≠0) : AnalyticAt ℂ transferC K :=
  ((Complex.analyticAt_cosh.comp analyticAt_fst).mul
    (Complex.analyticAt_cosh.comp analyticAt_snd)).div
    (Complex.analyticAt_sinh.comp analyticAt_fst) hS

theorem transferB_analyticAt {K : Coupling} (hS : S K≠0) : AnalyticAt ℂ transferB K :=
  (Complex.analyticAt_sinh.comp analyticAt_snd).div
    (Complex.analyticAt_sinh.comp analyticAt_fst) hS

theorem transferChart_analyticAt {K : Coupling} (hS : S K≠0) : AnalyticAt ℂ transferChart K :=
  (transferC_analyticAt hS).prod (transferB_analyticAt hS)

/-- Both directions of the regular transfer chart are genuinely complex analytic. -/
theorem exists_transfer_localAnalyticEquiv {K : Coupling} (hS : S K≠0) (hp : p K^2≠1) :
    ∃ e : OpenPartialHomeomorph Coupling Coupling,
      K∈e.source ∧ (e : Coupling → Coupling)=transferChart ∧
      AnalyticAt ℂ e K ∧ AnalyticAt ℂ e.symm (transferChart K) := by
  let d : Coupling ≃L[ℂ] Coupling := ContinuousLinearEquiv.ofBijective
    (transferDerivative K) (LinearMap.ker_eq_bot.mpr (transferDerivative_bijective hS hp).1)
    (LinearMap.range_eq_top.mpr (transferDerivative_bijective hS hp).2)
  have hd : HasStrictFDerivAt transferChart (d : Coupling →L[ℂ] Coupling) K :=
    hasStrictFDerivAt_transferChart hS
  let e := hd.toOpenPartialHomeomorph transferChart
  have he : (e : Coupling → Coupling)=transferChart := hd.toOpenPartialHomeomorph_coe
  have hK : K∈e.source := hd.mem_toOpenPartialHomeomorph_source
  have ha : AnalyticAt ℂ e K := by rw [he]; exact transferChart_analyticAt hS
  refine ⟨e,hK,he,ha,?_⟩
  rcases ha with ⟨ps,hps⟩
  have hp1 : ps 1=(continuousMultilinearCurryFin1 ℂ Coupling Coupling).symm
      (d : Coupling →L[ℂ] Coupling) := by
    apply (continuousMultilinearCurryFin1 ℂ Coupling Coupling).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hd' : HasFDerivAt (e : Coupling → Coupling) (d : Coupling →L[ℂ] Coupling) K := by
      rw [he]; exact hd.hasFDerivAt
    exact hps.hasFDerivAt.unique hd'
  have hg := (e.hasFPowerSeriesAt_symm hK hps hp1).analyticAt
  simpa only [he] using hg

end
end IsingBulk.Joint
