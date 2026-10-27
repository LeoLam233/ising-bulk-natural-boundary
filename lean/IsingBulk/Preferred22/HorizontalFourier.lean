import IsingBulk.Preferred22.VerticalLattice
import IsingBulk.HT.Contour.FourierTorusCoordinates

/-! Exact horizontal Fourier identification of the actual full site
coefficient. The only older input is a proper finite-dimensional torus shear
and Fourier coefficient formula, independent of old tails and endpoints. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def fixedVerticalDensity {N : ℕ} (s : ℂ) (b : ℤ) (θ : Fin N → ℝ) : ℂ :=
  regularAngularDensity s θ * (∏ i,angularRoots s θ i)^b.natAbs

theorem fixedVerticalDensity_congr_angles {N : ℕ} (s : ℂ) (b : ℤ)
    (θ φ : Fin N → ℝ) (h : ∀ i,angleRoot (θ i)=angleRoot (φ i)) :
    fixedVerticalDensity s b θ=fixedVerticalDensity s b φ := by
  have hy : (fun i => angleRoot (θ i))=(fun i => angleRoot (φ i)) := funext h
  have hz : angularRoots s θ=angularRoots s φ := by
    funext i
    simp only [angularRoots,angularW,cos_eq_of_angleRoot_eq (h i)]
  simp only [fixedVerticalDensity,regularAngularDensity,hy,hz]

theorem constrainedVerticalDensity_periodic (n : ℕ) (s : ℂ) (b : ℤ) :
    IsingBulk.First.CoordinatePeriodic n
      (fun θ => fixedVerticalDensity s b (constrainedAngles θ)) := by
  intro θ i
  apply fixedVerticalDensity_congr_angles
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [constrainedAngles,Fin.snoc_last]
    have hsum : (∑ j,Function.update θ i (θ i+2*Real.pi) j)=∑ j,θ j+2*Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) θ]
      ring
    rw [hsum,neg_add]
    exact angleRoot_periodic.sub_eq _
  · simp only [constrainedAngles,Fin.snoc_castSucc]
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self]
      exact angleRoot_periodic _
    · rw [Function.update_of_ne hji]

theorem fixedVerticalDensity_continuous {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 1 < ‖s‖) (b : ℤ) : Continuous (@fixedVerticalDensity N s b) := by
  have hZ : Continuous (fun θ : Fin N → ℝ => ∏ i,angularRoots s θ i) :=
    continuous_finsetProd _ (fun i _ =>
      (angularRoot_continuous hs).comp (continuous_apply i))
  exact (regularAngularDensity_continuous hN hs).mul (hZ.pow _)

theorem fixedVerticalDensity_periodic (N : ℕ) (s : ℂ) (b : ℤ) :
    IsingBulk.First.CoordinatePeriodic N (@fixedVerticalDensity N s b) := by
  intro θ i
  have hy : (fun j => angleRoot (Function.update θ i (θ i+2*Real.pi) j))=
      (fun j => angleRoot (θ j)) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self]
      exact angleRoot_periodic _
    · rw [Function.update_of_ne hji]
  have hz : angularRoots s (Function.update θ i (θ i+2*Real.pi))=angularRoots s θ := by
    funext j
    have hc := cos_eq_of_angleRoot_eq (congrFun hy j)
    simp only [angularRoots,angularW,hc]
  simp only [fixedVerticalDensity,regularAngularDensity,hy,hz]

theorem angularBox_integral_eq_multiAngleIntegral {N : ℕ}
    (F : (Fin N → ℝ) → ℂ) (hF : Continuous F)
    (hp : IsingBulk.First.CoordinatePeriodic N F) :
    (∫ θ in angularBox N,F θ)=IsingBulk.First.multiAngleIntegral N F := by
  rw [angularBox_integral_eq_shifted_box,IsingBulk.First.multiAngleIntegral_eq_box N F hF]
  simpa only [sub_eq_add_neg] using
    IsingBulk.First.angleBox_integral_shift N F hF hp (fun _ => -Real.pi)

theorem horizontalExponential_periodic (N : ℕ) (a : ℤ) :
    IsingBulk.First.CoordinatePeriodic N
      (fun θ : Fin N → ℝ => exp (I*(a:ℂ)*(∑ j,(θ j:ℂ)))) := by
  intro θ i
  have hr : (∑ j,Function.update θ i (θ i+2*Real.pi) j)=∑ j,θ j+2*Real.pi := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) θ]
    ring
  have hc : (∑ j,(Function.update θ i (θ i+2*Real.pi) j:ℂ))=
      (∑ j,(θ j:ℂ))+2*(Real.pi:ℂ) := by exact_mod_cast hr
  dsimp only
  rw [hc,mul_add,Complex.exp_add,
    show I*(a:ℂ)*(2*(Real.pi:ℂ))=(a:ℂ)*(2*(Real.pi:ℂ)*I) by ring,
    Complex.exp_int_mul_two_pi_mul_I,mul_one]

theorem horizontalExponential_continuous (N : ℕ) (a : ℤ) :
    Continuous (fun θ : Fin N → ℝ => exp (I*(a:ℂ)*(∑ j,(θ j:ℂ)))) :=
  (continuous_const.mul (continuous_finsetSum _ (fun i _ =>
    Complex.continuous_ofReal.comp (continuous_apply i)))).cexp

/-- Exact actual-site Fourier coefficient, including N!, (2pi)^N, the
negative Fourier index, every particle and both displacement signs. -/
theorem siteCoefficient_eq_fourier (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖) (a b : ℤ) :
    siteCoefficient (n+1) a b s = ((n+1).factorial:ℂ)⁻¹ *
      fourierCoeff (IsingBulk.HT.Contour.torusMeanCircle n
        (fixedVerticalDensity s b)
        (fixedVerticalDensity_continuous (Nat.succ_pos n) hs b)
        (fixedVerticalDensity_periodic (n+1) s b)) (-a) := by
  let F := @fixedVerticalDensity (n+1) s b
  have hF : Continuous F := fixedVerticalDensity_continuous (Nat.succ_pos n) hs b
  have hp : IsingBulk.First.CoordinatePeriodic (n+1) F := fixedVerticalDensity_periodic _ s b
  let H : (Fin (n+1) → ℝ) → ℂ := fun θ => F θ*exp (I*(a:ℂ)*(∑ i,(θ i:ℂ)))
  have hH : Continuous H := hF.mul (horizontalExponential_continuous _ a)
  have hHp : IsingBulk.First.CoordinatePeriodic (n+1) H := by
    intro θ i
    change F (Function.update θ i (θ i+2*Real.pi))*_ = F θ*_
    rw [hp θ i]
    exact congrArg (fun z => F θ*z) (horizontalExponential_periodic (n+1) a θ i)
  have he : (fun θ : Fin (n+1) → ℝ =>
      exp (I*(a:ℂ)*(∑ i,(θ i:ℂ)))*(∏ i,angularRoots s θ i)^b.natAbs *
      (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det *
      ∏ i,oneBody (angularRoots s θ i))=H := by
    funext θ
    dsimp only [H,F,fixedVerticalDensity,regularAngularDensity]
    ring
  unfold siteCoefficient
  rw [he,angularBox_integral_eq_multiAngleIntegral H hH hHp,mul_inv_rev,← inv_pow]
  have hf := IsingBulk.HT.Contour.torus_exponential_coefficient n F hF hp a
  change ((2*(Real.pi:ℂ))⁻¹)^(n+1)*((n+1).factorial:ℂ)⁻¹ *
    IsingBulk.First.multiAngleIntegral (n+1) H = _
  calc
    _ = ((n+1).factorial:ℂ)⁻¹ *
        (((2*(Real.pi:ℂ))⁻¹)^(n+1)*IsingBulk.First.multiAngleIntegral (n+1) H) := by ring
    _ = _ := congrArg (fun z => ((n+1).factorial:ℂ)⁻¹*z) hf

/-- Fourier inversion for the actual horizontal lattice row, after the
row's genuine summability has been established. -/
theorem horizontal_site_tsum (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖) (b : ℤ)
    (hq : Summable (fun a : ℤ => siteCoefficient (n+1) a b s)) :
    (∑' a : ℤ,siteCoefficient (n+1) a b s)=constrainedVerticalCoefficient n b s := by
  let F := @fixedVerticalDensity (n+1) s b
  let hc := fixedVerticalDensity_continuous (Nat.succ_pos n) hs b
  let hp := fixedVerticalDensity_periodic (n+1) s b
  let f := IsingBulk.HT.Contour.torusMeanCircle n F hc hp
  have hfac : ((n+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  have he (a : ℤ) : ((n+1).factorial:ℂ)*siteCoefficient (n+1) a b s=fourierCoeff f (-a) := by
    rw [siteCoefficient_eq_fourier n hs a b]
    simp only [← mul_assoc,mul_inv_cancel₀ hfac,one_mul]
    rfl
  have hsum : Summable (fourierCoeff f) := by
    have hh := (hq.mul_left ((n+1).factorial:ℂ)).comp_injective
      (neg_injective : Function.Injective (fun a : ℤ => -a))
    exact hh.congr (fun a => by simpa only [Function.comp_apply,neg_neg] using he (-a))
  have hzero : (∑' a : ℤ,fourierCoeff f a)=f 0 := by
    simpa only [fourier_eval_zero,smul_eq_mul,mul_one] using
      (has_pointwise_sum_fourier_series_of_summable hsum (0 : AddCircle (2*Real.pi))).tsum_eq
  have hreindex : (∑' a : ℤ,fourierCoeff f (-a))=∑' a : ℤ,fourierCoeff f a :=
    (Equiv.neg ℤ).tsum_eq (fourierCoeff f)
  calc
    (∑' a : ℤ,siteCoefficient (n+1) a b s) =
        ((n+1).factorial:ℂ)⁻¹*(∑' a : ℤ,fourierCoeff f (-a)) := by
      simp_rw [siteCoefficient_eq_fourier n hs]
      rw [tsum_mul_left]
    _ = ((n+1).factorial:ℂ)⁻¹*f 0 := by rw [hreindex,hzero]
    _ = constrainedVerticalCoefficient n b s := by
      rw [IsingBulk.HT.Contour.torusMeanCircle_zero]
      have hi : IsingBulk.First.multiAngleIntegral n
          (fun θ : Fin n → ℝ => F (IsingBulk.First.shapeExtend θ))=
          ∫ θ in angularBox n,fixedVerticalDensity s b (constrainedAngles θ) :=
        (angularBox_integral_eq_multiAngleIntegral _
          (hc.comp (constrainedAngles_continuous n))
          (constrainedVerticalDensity_periodic n s b)).symm
      rw [hi]
      simp only [constrainedVerticalCoefficient,fixedVerticalDensity,mul_inv_rev,← inv_pow]
      ring

end
end IsingBulk.Preferred22
