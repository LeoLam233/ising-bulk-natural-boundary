import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The source's exact 4/3 convolution estimate on the angular circle.
Two genuine Cauchy--Schwarz inequalities and Haar integration establish the
four-factor constrained bound; no Young inequality is assumed as input. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Convolution

variable {T : ℝ} [Fact (0<T)]

def preferredCircleConvolution (f g : AddCircle T → ℝ) : AddCircle T → ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume

@[simp] theorem preferredCircleConvolution_apply (f g : AddCircle T → ℝ) (x : AddCircle T) :
    preferredCircleConvolution f g x=∫ y,f y*g (x-y) := rfl

theorem preferredCircle_integrable {f : AddCircle T → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem preferredCircleConvolution_continuous {f g : AddCircle T → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (preferredCircleConvolution f g) :=
  (HasCompactSupport.of_compactSpace g).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (preferredCircle_integrable hf).locallyIntegrable hg

theorem preferredCircleConvolution_nonneg {f g : AddCircle T → ℝ}
    (hf : ∀ x,0≤f x) (hg : ∀ x,0≤g x) (x : AddCircle T) :
    0≤preferredCircleConvolution f g x := integral_nonneg (fun y => mul_nonneg (hf y) (hg (x-y)))

theorem preferredCircleConvolution_integral {f g : AddCircle T → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x,preferredCircleConvolution f g x)=(∫ x,f x)*(∫ x,g x) :=
  integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (preferredCircle_integrable hf) (preferredCircle_integrable hg)

/-- Cauchy--Schwarz with its two actual square integrals. -/
theorem preferredCircle_integral_mul_sq_le {f g : AddCircle T → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x,0≤f x) (hg0 : ∀ x,0≤g x) :
    (∫ x,f x*g x)^2≤(∫ x,(f x)^2)*(∫ x,(g x)^2) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure (AddCircle T))) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  simp only [Real.rpow_ofNat,←Real.sqrt_eq_rpow] at h
  have hC : 0≤∫ x,f x*g x := integral_nonneg (fun x => mul_nonneg (hf0 x) (hg0 x))
  have hh := pow_le_pow_left₀ hC h 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))] at hh
  exact hh

/-- Haar translation identifies the two square integrals exactly. -/
theorem preferredCircleConvolution_self_le_sq_integral {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (x : AddCircle T) :
    preferredCircleConvolution f f x≤∫ y,(f y)^2 := by
  have hcs := preferredCircle_integral_mul_sq_le hf (hf.comp (by fun_prop : Continuous (fun y => x-y)))
    hf0 (fun y => hf0 (x-y))
  simp only [Function.comp_apply] at hcs
  rw [integral_sub_left_eq_self (fun y => (f y)^2) volume x] at hcs
  have hC := preferredCircleConvolution_nonneg hf0 hf0 x
  have hF : 0≤∫ y,(f y)^2 := integral_nonneg (fun y => sq_nonneg (f y))
  change (preferredCircleConvolution f f x)^2≤(∫ y,(f y)^2)*(∫ y,(f y)^2) at hcs
  nlinarith

theorem preferred_rpow_two_thirds_sq {u : ℝ} (hu : 0≤u) :
    (u^(2/3:ℝ))^2=u^(4/3:ℝ) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hu]
  norm_num

theorem preferred_rpow_one_third_sq {u : ℝ} (hu : 0≤u) :
    (u^(1/3:ℝ))^2=u^(2/3:ℝ) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hu]
  norm_num

/-- The exact pointwise step of Lemma 5.2. Its source factor is the actual
4/3 mass, not a product of incorrectly independent constrained factors. -/
theorem preferredCircleConvolution_four_thirds_pointwise {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (x : AddCircle T) :
    (preferredCircleConvolution f f x)^2≤
      (∫ y,(f y)^(4/3:ℝ))*preferredCircleConvolution (fun y => (f y)^(4/3:ℝ))
        (fun y => (f y)^(4/3:ℝ)) x := by
  let a := fun y : AddCircle T => (f y)^(2/3:ℝ)
  have hac : Continuous a := hf.rpow_const (fun _ => Or.inr (by norm_num))
  have ha0 (y : AddCircle T) : 0≤a y := Real.rpow_nonneg (hf0 y) _
  have ha := preferredCircleConvolution_self_le_sq_integral hac ha0 x
  have hasq (y : AddCircle T) : (a y)^2=(f y)^(4/3:ℝ) := preferred_rpow_two_thirds_sq (hf0 y)
  simp_rw [hasq] at ha
  let u := fun y : AddCircle T => (f y*f (x-y))^(2/3:ℝ)
  let v := fun y : AddCircle T => (f y*f (x-y))^(1/3:ℝ)
  have hbase : Continuous (fun y : AddCircle T => f y*f (x-y)) := by fun_prop
  have hu : Continuous u := hbase.rpow_const (fun _ => Or.inr (by norm_num))
  have hv : Continuous v := hbase.rpow_const (fun _ => Or.inr (by norm_num))
  have hu0 (y : AddCircle T) : 0≤u y := Real.rpow_nonneg (mul_nonneg (hf0 y) (hf0 (x-y))) _
  have hv0 (y : AddCircle T) : 0≤v y := Real.rpow_nonneg (mul_nonneg (hf0 y) (hf0 (x-y))) _
  have hcs := preferredCircle_integral_mul_sq_le hu hv hu0 hv0
  have huv (y : AddCircle T) : u y*v y=f y*f (x-y) := by
    dsimp [u,v]
    rw [←Real.rpow_add_of_nonneg (mul_nonneg (hf0 y) (hf0 (x-y))) (by norm_num) (by norm_num)]
    norm_num
  have hu2 (y : AddCircle T) : (u y)^2=(f y)^(4/3:ℝ)*(f (x-y))^(4/3:ℝ) := by
    rw [preferred_rpow_two_thirds_sq (mul_nonneg (hf0 y) (hf0 (x-y))),Real.mul_rpow (hf0 y) (hf0 (x-y))]
  have hv2 (y : AddCircle T) : (v y)^2=a y*a (x-y) := by
    rw [preferred_rpow_one_third_sq (mul_nonneg (hf0 y) (hf0 (x-y))),Real.mul_rpow (hf0 y) (hf0 (x-y))]
  simp_rw [huv,hu2,hv2] at hcs
  change (preferredCircleConvolution f f x)^2≤
    preferredCircleConvolution (fun y => (f y)^(4/3:ℝ)) (fun y => (f y)^(4/3:ℝ)) x*
      preferredCircleConvolution a a x at hcs
  have hnn := preferredCircleConvolution_nonneg (fun y => Real.rpow_nonneg (hf0 y) (4/3:ℝ))
    (fun y => Real.rpow_nonneg (hf0 y) (4/3:ℝ)) x
  exact hcs.trans ((mul_le_mul_of_nonneg_left ha hnn).trans_eq (mul_comm _ _))

/-- The genuine Young 4/3 * 4/3 -> 2 special case on the angular circle. -/
theorem preferredCircleConvolution_four_thirds_square_integral {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) :
    (∫ x,(preferredCircleConvolution f f x)^2)≤(∫ x,(f x)^(4/3:ℝ))^3 := by
  let F := ∫ x,(f x)^(4/3:ℝ)
  let h := fun x : AddCircle T => (f x)^(4/3:ℝ)
  have hc : Continuous h := hf.rpow_const (fun _ => Or.inr (by norm_num))
  have hi : Integrable (fun x => (preferredCircleConvolution f f x)^2) :=
    preferredCircle_integrable ((preferredCircleConvolution_continuous hf hf).pow 2)
  have hhi : Integrable (fun x => F*preferredCircleConvolution h h x) :=
    (preferredCircle_integrable (preferredCircleConvolution_continuous hc hc)).const_mul F
  calc
    _ ≤ ∫ x,F*preferredCircleConvolution h h x :=
      integral_mono hi hhi (fun x => preferredCircleConvolution_four_thirds_pointwise hf hf0 x)
    _ = F*(F*F) := by rw [integral_const_mul,preferredCircleConvolution_integral hc hc]
    _ = _ := by dsimp [F]; ring

/-- Four genuine constrained factors have a bounded convolution at every
point, with exactly the cube of the actual 4/3 mass. -/
theorem preferredCircle_fourfold_convolution_bound {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (x : AddCircle T) :
    preferredCircleConvolution (preferredCircleConvolution f f) (preferredCircleConvolution f f) x≤
      (∫ y,(f y)^(4/3:ℝ))^3 :=
  (preferredCircleConvolution_self_le_sq_integral (preferredCircleConvolution_continuous hf hf)
    (preferredCircleConvolution_nonneg hf0 hf0) x).trans
    (preferredCircleConvolution_four_thirds_square_integral hf hf0)

end
end IsingBulk.Preferred22
