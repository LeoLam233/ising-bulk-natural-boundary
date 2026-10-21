import IsingBulk.First.AngularCoordinateSplit
import IsingBulk.First.PeriodicBoxIntegral
import IsingBulk.First.MeanCoordinates
import Mathlib.Analysis.Fourier.AddCircle

/-!
The total-angle coordinate on the torus is an integer shear, not the
non-unimodular division-by-particle-number mean chart.  The dependent angle
is the final coordinate, exactly as in the physical angular coefficient.
Fubini and periodic translation prove the measure identity below.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- An integral unimodular shear with total angle `u`. -/
def torusTotalAngle {n : ℕ} (u : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc x (u-∑ i, x i)

@[simp] theorem sum_torusTotalAngle {n : ℕ} (u : ℝ) (x : Fin n → ℝ) :
    ∑ i, torusTotalAngle u x i = u := by
  rw [Fin.sum_univ_castSucc]
  simp only [torusTotalAngle,Fin.snoc_castSucc,Fin.snoc_last]
  ring

@[simp] theorem torusTotalAngle_zero {n : ℕ} (x : Fin n → ℝ) :
    torusTotalAngle 0 x = shapeExtend x := by
  simp only [torusTotalAngle,shapeExtend,zero_sub]

theorem continuous_torusTotalAngle (n : ℕ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => torusTotalAngle p.1 p.2) := by
  unfold torusTotalAngle
  fun_prop

theorem coordinatePeriodic_snoc_last {n : ℕ} {F : (Fin (n+1) → ℝ) → ℂ}
    (hF : CoordinatePeriodic (n+1) F) (x : Fin n → ℝ) :
    Function.Periodic (fun u : ℝ => F (Fin.snoc x u)) (2*Real.pi) := by
  intro u
  simpa only [Fin.snoc_last,Fin.update_snoc_last] using hF (Fin.snoc x u) (Fin.last n)

/-- Genuine finite Fubini, with the total angle outside the shape box. -/
theorem angleBox_interval_integral_swap (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℂ) (hF : Continuous F) :
    (∫ x in angleBox n, ∫ u : ℝ in 0..2*Real.pi, F (u,x)) =
      ∫ u : ℝ in 0..2*Real.pi, ∫ x in angleBox n, F (u,x) := by
  have hi : IntegrableOn F (Icc (0:ℝ) (2*Real.pi) ×ˢ angleBox n)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_prod_reverse volume volume F _ _ hi).symm.trans (setIntegral_prod F hi)

/-- Only periodicity in the final coordinate is needed for the shear. -/
theorem multiAngleIntegral_totalAngle (n : ℕ)
    (F : (Fin (n+1) → ℝ) → ℂ) (hF : Continuous F)
    (hperiod : ∀ x : Fin n → ℝ,
      Function.Periodic (fun u : ℝ => F (Fin.snoc x u)) (2*Real.pi)) :
    multiAngleIntegral (n+1) F =
      ∫ u : ℝ in 0..2*Real.pi, multiAngleIntegral n (fun x => F (torusTotalAngle u x)) := by
  have hcomp : Continuous (fun p : ℝ × (Fin n → ℝ) => F (torusTotalAngle p.1 p.2)) :=
    hF.comp (continuous_torusTotalAngle n)
  have hshift (x : Fin n → ℝ) :
      (∫ u : ℝ in 0..2*Real.pi, F (Fin.snoc x u)) =
        ∫ u : ℝ in 0..2*Real.pi, F (torusTotalAngle u x) := by
    symm
    unfold torusTotalAngle
    simp_rw [sub_eq_add_neg]
    rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => F (Fin.snoc x u))
      (-(∑ i, x i))]
    simpa only [zero_add,add_comm (2*Real.pi) (-(∑ i, x i))] using
      (hperiod x).intervalIntegral_add_eq (-(∑ i, x i)) 0
  rw [multiAngleIntegral_eq_box (n+1) F hF,
    angleBox_integral_succAbove n (Fin.last n) F hF]
  simp only [Fin.insertNth_last']
  simp_rw [hshift]
  rw [angleBox_interval_integral_swap n _ hcomp]
  apply intervalIntegral.integral_congr
  intro u _
  exact (multiAngleIntegral_eq_box n _
    (hcomp.comp (continuous_const.prodMk continuous_id))).symm

/-- The continuous marginal on a total-angle slice, including its exact
`(2π)^(-n)` normalization. -/
def torusMeanSlice (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ) (u : ℝ) : ℂ :=
  ((2*Real.pi:ℂ)⁻¹)^n * multiAngleIntegral n (fun x => F (torusTotalAngle u x))

theorem torusMeanSlice_continuous (n : ℕ)
    (F : (Fin (n+1) → ℝ) → ℂ) (hF : Continuous F) :
    Continuous (torusMeanSlice n F) := by
  exact continuous_const.mul (continuous_multiAngleIntegral n _
    (hF.comp (continuous_torusTotalAngle n)))

theorem torusMeanSlice_periodic (n : ℕ)
    (F : (Fin (n+1) → ℝ) → ℂ) (hF : CoordinatePeriodic (n+1) F) :
    Function.Periodic (torusMeanSlice n F) (2*Real.pi) := by
  intro u
  unfold torusMeanSlice
  apply congrArg (fun G => ((2*Real.pi:ℂ)⁻¹)^n * multiAngleIntegral n G)
  funext x
  change F (Fin.snoc x (u+2*Real.pi-∑ i, x i)) = F (Fin.snoc x (u-∑ i, x i))
  rw [show u+2*Real.pi-∑ i, x i = (u-∑ i, x i)+2*Real.pi by ring]
  exact coordinatePeriodic_snoc_last hF x (u-∑ i, x i)

/-- The actual continuous circle marginal; continuity at the seam is
proved from periodicity rather than supplied as an interface hypothesis. -/
def torusMeanCircle (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : Continuous F) (hperiod : CoordinatePeriodic (n+1) F) :
    C(AddCircle (2*Real.pi),ℂ) where
  toFun := AddCircle.liftIco (2*Real.pi) 0 (torusMeanSlice n F)
  continuous_toFun := AddCircle.liftIco_zero_continuous
    (by simpa only [zero_add] using (torusMeanSlice_periodic n F hperiod 0).symm)
    (torusMeanSlice_continuous n F hF).continuousOn

@[simp] theorem torusMeanCircle_zero (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : Continuous F) (hperiod : CoordinatePeriodic (n+1) F) :
    torusMeanCircle n F hF hperiod 0 =
      ((2*Real.pi:ℂ)⁻¹)^n * multiAngleIntegral n (fun x => F (shapeExtend x)) := by
  change AddCircle.liftIco (2*Real.pi) 0 (torusMeanSlice n F) (0 : AddCircle (2*Real.pi)) = _
  rw [← AddCircle.coe_zero,AddCircle.liftIco_zero_coe_apply (show (0:ℝ)∈Ico 0 (2*Real.pi) from
    ⟨le_rfl,Real.two_pi_pos⟩)]
  simp only [torusMeanSlice,torusTotalAngle_zero]

theorem torus_multiAngleIntegral_mul_const (n : ℕ)
    (F : (Fin n → ℝ) → ℂ) (a : ℂ) :
    multiAngleIntegral n (fun x => F x*a) = multiAngleIntegral n F*a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [multiAngleIntegral,intervalIntegral.integral_mul_const]
    exact ih _

/-- The sign is negative because the physical coefficient uses `exp(+iku)`. -/
theorem torusMeanCircle_fourierCoeff (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : Continuous F) (hperiod : CoordinatePeriodic (n+1) F) (k : ℤ) :
    fourierCoeff (torusMeanCircle n F hF hperiod) (-k) =
      (2*Real.pi:ℂ)⁻¹ * ∫ u : ℝ in 0..2*Real.pi,
        fourier k (u : AddCircle (2*Real.pi))*torusMeanSlice n F u := by
  change fourierCoeff (AddCircle.liftIco (2*Real.pi) 0 (torusMeanSlice n F)) (-k) = _
  rw [fourierCoeff_liftIco_eq,fourierCoeffOn_eq_integral]
  simp [Complex.real_smul]

theorem fourier_twoPi_eq_exp (k : ℤ) (u : ℝ) :
    fourier k (u : AddCircle (2*Real.pi)) =
      Complex.exp (Complex.I*(k:ℂ)*(u:ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hpi]

/-- Exact normalized total-angle Fourier coefficient after the torus shear.
No Fourier inversion, summability, or unknown lattice identity is assumed. -/
theorem torus_fourier_coefficient (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : Continuous F) (hperiod : CoordinatePeriodic (n+1) F) (k : ℤ) :
    ((2*Real.pi:ℂ)⁻¹)^(n+1) * multiAngleIntegral (n+1)
      (fun x => F x * fourier k ((∑ i, x i : ℝ) : AddCircle (2*Real.pi))) =
      fourierCoeff (torusMeanCircle n F hF hperiod) (-k) := by
  let H : (Fin (n+1) → ℝ) → ℂ := fun x =>
    F x * fourier k ((∑ i, x i : ℝ) : AddCircle (2*Real.pi))
  have hH : Continuous H := hF.mul ((map_continuous (fourier k)).comp
    ((AddCircle.continuous_mk' (2*Real.pi)).comp (by fun_prop)))
  have hHperiod (x : Fin n → ℝ) :
      Function.Periodic (fun u : ℝ => H (Fin.snoc x u)) (2*Real.pi) := by
    intro u
    dsimp only [H]
    have hp := coordinatePeriodic_snoc_last hperiod x u
    change F (Fin.snoc x (u+2*Real.pi)) = F (Fin.snoc x u) at hp
    rw [hp]
    congr 1
    simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
    rw [show (∑ i, x i)+(u+2*Real.pi)=((∑ i, x i)+u)+2*Real.pi by ring,
      AddCircle.coe_add_period]
  have hshear := multiAngleIntegral_totalAngle n H hH hHperiod
  have hinner (u : ℝ) :
      multiAngleIntegral n (fun x => H (torusTotalAngle u x)) =
        multiAngleIntegral n (fun x => F (torusTotalAngle u x)) *
          fourier k (u : AddCircle (2*Real.pi)) := by
    simp only [H,sum_torusTotalAngle]
    exact torus_multiAngleIntegral_mul_const n _ _
  change ((2*Real.pi:ℂ)⁻¹)^(n+1) * multiAngleIntegral (n+1) H = _
  rw [hshear]
  simp_rw [hinner]
  rw [torusMeanCircle_fourierCoeff]
  unfold torusMeanSlice
  have he : (fun u : ℝ => fourier k (u : AddCircle (2*Real.pi)) *
      (((2*Real.pi:ℂ)⁻¹)^n * multiAngleIntegral n (fun x => F (torusTotalAngle u x)))) =
      (fun u : ℝ => ((2*Real.pi:ℂ)⁻¹)^n *
        (multiAngleIntegral n (fun x => F (torusTotalAngle u x)) *
          fourier k (u : AddCircle (2*Real.pi)))) := by
    funext u
    ring
  rw [he,intervalIntegral.integral_const_mul,pow_succ]
  ring

/-- The literal physical exponential convention, with its normalization and
negative Fourier index fully resolved. -/
theorem torus_exponential_coefficient (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : Continuous F) (hperiod : CoordinatePeriodic (n+1) F) (k : ℤ) :
    ((2*Real.pi:ℂ)⁻¹)^(n+1) * multiAngleIntegral (n+1)
      (fun x => F x * Complex.exp (Complex.I*(k:ℂ)*(∑ i,(x i:ℂ)))) =
      fourierCoeff (torusMeanCircle n F hF hperiod) (-k) := by
  rw [← torus_fourier_coefficient n F hF hperiod k]
  apply congrArg (fun G => ((2*Real.pi:ℂ)⁻¹)^(n+1) * multiAngleIntegral (n+1) G)
  funext x
  rw [fourier_twoPi_eq_exp]
  push_cast
  rfl

end
end IsingBulk.HT.Contour
