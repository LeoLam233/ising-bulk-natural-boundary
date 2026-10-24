import IsingBulk.Anisotropic.NegativeNormalForm.UniformDerivativeBounds
import IsingBulk.Anisotropic.NegativeNormalForm.CanonicalNormalForm

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

@[simp] theorem norm_scalarConfiguration {n : ℕ} (a : ℂ) (v : Config n) :
    ‖scalarConfiguration a v‖=‖a‖*‖v‖ := norm_smul a v

 theorem scalarConfiguration_sub_identity {n : ℕ} (a : ℂ) (v : Config n) :
    scalarConfiguration a v-v=(a-1) • v := by
  change a • v-v=(a-1) • v
  module

 theorem hessian_inverse_sqrt_uniform (B : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) :
    ∃ r : ℝ, 0<r ∧ ∀ d : ℂ, ‖d‖<r → centralHessian B phi d≠0 ∧
      ‖(Complex.sqrt (centralHessian B phi d))⁻¹-1‖≤1/64 ∧
      ‖(Complex.sqrt (centralHessian B phi d))⁻¹‖≤9/8 := by
  have hs : AnalyticAt ℂ (fun d => Complex.sqrt (centralHessian B phi d)) 0 :=
    sqrt_analyticAt_one.comp_of_eq (centralHessian_analyticAt_zero B phi hB) (centralHessian_zero B phi)
  have hi := hs.inv (by simp [centralHessian_zero])
  have hb : ∀ᶠ d : ℂ in 𝓝 0, ‖(Complex.sqrt (centralHessian B phi d))⁻¹-1‖<1/64 := by
    have hh := (hi.continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (show ‖(Complex.sqrt (centralHessian B phi 0))⁻¹-1‖<(1/64:ℝ) by simp [centralHessian_zero])
    exact hh
  have hall := hb.and (centralHessian_eventually_nonzero B phi hB)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r,hr,?_⟩
  intro d hd
  have hh := hball (show d∈ball (0:ℂ) r by simpa using hd)
  refine ⟨hh.2,hh.1.le,?_⟩
  have ht := norm_le_norm_sub_add ((Complex.sqrt (centralHessian B phi d))⁻¹) 1
  rw [norm_one] at ht
  linarith [hh.1]

 theorem scalar_rescaled_perturbation_lipschitz {n : ℕ} (F : Config n → Config n)
    (a : ℂ) (r s : ℝ) (_hs : 0≤s) (ha : ‖a‖≤9/8) (ha1 : ‖a-1‖≤1/64)
    (hsr : (9/8)*s≤r)
    (hF : LipschitzOnWith (3/32) (fun x => F x-x) (closedBall 0 r)) :
    LipschitzOnWith (1/8) (fun y => F (scalarConfiguration a y)-y) (closedBall 0 s) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hy' : ‖y‖≤s := by simpa using hy
  have hz' : ‖z‖≤s := by simpa using hz
  have hinside (v : Config n) (hv : ‖v‖≤s) : scalarConfiguration a v∈closedBall 0 r := by
    simp only [mem_closedBall,dist_zero_right,norm_scalarConfiguration]
    exact (mul_le_mul ha hv (norm_nonneg _) (by norm_num)).trans hsr
  have h := hF.dist_le_mul (scalarConfiguration a y) (hinside y hy') (scalarConfiguration a z) (hinside z hz')
  simp only [dist_eq_norm,← map_sub,norm_scalarConfiguration,NNReal.coe_div,NNReal.coe_ofNat] at h
  have he : (F (scalarConfiguration a y)-y)-(F (scalarConfiguration a z)-z)=
      ((F (scalarConfiguration a y)-scalarConfiguration a y)-(F (scalarConfiguration a z)-scalarConfiguration a z))+
      (a-1) • (y-z) := by
    rw [smul_sub,← scalarConfiguration_sub_identity,← scalarConfiguration_sub_identity]
    abel
  have ht := norm_add_le
    ((F (scalarConfiguration a y)-scalarConfiguration a y)-(F (scalarConfiguration a z)-scalarConfiguration a z))
    ((a-1) • (y-z))
  rw [← he,norm_smul] at ht
  simp only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
  have hmul := mul_le_mul_of_nonneg_right ha (norm_nonneg (y-z))
  have hmul1 := mul_le_mul_of_nonneg_right ha1 (norm_nonneg (y-z))
  nlinarith [norm_nonneg (y-z)]

end
end IsingBulk.Anisotropic.NegativeNormalForm
