import IsingBulk.Preferred22.CircleConstrained
import Mathlib.Analysis.MeanInequalities

namespace IsingBulk.HT22.LocalLimit.ThreeParticleSelected
noncomputable section
open Set MeasureTheory Filter IsingBulk.Preferred22
open scoped BigOperators Topology ENNReal

theorem triple_pointwise {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    3*(a*b*c) ≤ a^(3/2:ℝ)*b^(3/2:ℝ)+b^(3/2:ℝ)*c^(3/2:ℝ)+a^(3/2:ℝ)*c^(3/2:ℝ) := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁:=1/3) (w₂:=1/3) (w₃:=1/3)
    (p₁:=a^(3/2:ℝ)*b^(3/2:ℝ)) (p₂:=b^(3/2:ℝ)*c^(3/2:ℝ))
    (p₃:=a^(3/2:ℝ)*c^(3/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by norm_num)
  have half (x : ℝ) (hx : 0≤x) : (x^(3/2:ℝ))^(1/3:ℝ)=Real.sqrt x := by
    rw [←Real.rpow_mul hx]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),half a ha,half b hb,half c hc] at h
  have he : (Real.sqrt a*Real.sqrt b)*(Real.sqrt b*Real.sqrt c)*(Real.sqrt a*Real.sqrt c)=a*b*c := by
    calc
      _ = (Real.sqrt a)^2*(Real.sqrt b)^2*(Real.sqrt c)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hc]
  rw [he] at h
  linarith

variable {T : ℝ} [Fact (0<T)]

/-- Three actual constrained factors: the symmetric Young 3/2 bound follows
from pointwise AM-GM and exact Haar translations, without a fourth factor. -/
theorem triple_convolution_bound {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (q : AddCircle T) :
    preferredCircleConvolution f (preferredCircleConvolution f f) q≤
      (∫ x,(f x)^(3/2:ℝ))^2 := by
  let F := fun x : AddCircle T => (f x)^(3/2:ℝ)
  let M := ∫ x,F x
  have hF : Continuous F := hf.rpow_const (fun _ => Or.inr (by norm_num))
  have hpoint (x : AddCircle T) :
      3*(f x*preferredCircleConvolution f f (q-x))≤
        F x*M+preferredCircleConvolution F F (q-x)+F x*M := by
    have hmono := integral_mono
      (preferredCircle_integrable (show Continuous (fun y => 3*(f x*f y*f (q-x-y))) by fun_prop))
      (preferredCircle_integrable (show Continuous (fun y => F x*F y+F y*F (q-x-y)+F x*F (q-x-y)) by fun_prop))
      (fun y => triple_pointwise (hf0 x) (hf0 y) (hf0 (q-x-y)))
    have heL : (∫ y : AddCircle T,3*(f x*f y*f (q-x-y)))=
        3*(f x*preferredCircleConvolution f f (q-x)) := by
      simp only [preferredCircleConvolution_apply,←integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by ring
    have heR : (∫ y : AddCircle T,F x*F y+F y*F (q-x-y)+F x*F (q-x-y))=
        F x*M+preferredCircleConvolution F F (q-x)+F x*M := by
      rw [integral_add (preferredCircle_integrable (by fun_prop)) (preferredCircle_integrable (by fun_prop)),
        integral_add (preferredCircle_integrable (by fun_prop)) (preferredCircle_integrable (by fun_prop)),
        integral_const_mul,integral_const_mul,integral_sub_left_eq_self F volume (q-x)]
      rfl
    rwa [heL,heR] at hmono
  have hconv := preferredCircleConvolution_continuous hf hf
  have hconvF := preferredCircleConvolution_continuous hF hF
  have hmono := integral_mono
    (preferredCircle_integrable (show Continuous (fun x => 3*(f x*preferredCircleConvolution f f (q-x))) by fun_prop))
    (preferredCircle_integrable (show Continuous (fun x => F x*M+preferredCircleConvolution F F (q-x)+F x*M) by fun_prop)) hpoint
  have heL : (∫ x : AddCircle T,3*(f x*preferredCircleConvolution f f (q-x)))=
      3*preferredCircleConvolution f (preferredCircleConvolution f f) q := by
    rw [integral_const_mul];rfl
  have heR : (∫ x : AddCircle T,F x*M+preferredCircleConvolution F F (q-x)+F x*M)=3*M^2 := by
    rw [integral_add (preferredCircle_integrable (by fun_prop)) (preferredCircle_integrable (by fun_prop)),
      integral_add (preferredCircle_integrable (by fun_prop)) (preferredCircle_integrable (by fun_prop)),
      integral_mul_const,
      integral_sub_left_eq_self (preferredCircleConvolution F F) volume q,
      preferredCircleConvolution_integral hF hF]
    dsimp [M]
    ring
  rw [heL,heR] at hmono
  change 3*preferredCircleConvolution f (preferredCircleConvolution f f) q ≤
    3*(∫ x,(f x)^(3/2:ℝ))^2 at hmono
  linarith

end
end IsingBulk.HT22.LocalLimit.ThreeParticleSelected
