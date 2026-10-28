import IsingBulk.HT22.Physical.ContourReflection
import IsingBulk.HT22.Physical.ComplexAnalytic
import IsingBulk.Preferred22.PhysicalTransport

namespace IsingBulk.HT22.Physical
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem bareContourDensity_continuous (negative : Bool) {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (t : ℂ) (ht : t≠0)
    (hW : ∀ θ : Fin N → ℝ, ∀ i, OffRealSegment
      (t+t⁻¹-Complex.cos (deformedAngles τ p m θ i))) :
    Continuous (bareContourDensity negative τ p m t (N := N)) := by
  have hw : Continuous (deformedAngles τ p m (N := N)) := by
    unfold deformedAngles balancedShift occupancy
    fun_prop
  have hd : Continuous (fun θ : Fin N → ℝ =>
      complexSignedDensity negative (t,deformedAngles τ p m θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (complexSignedDensity_analyticAt_of_off_segment negative hN ht _ (hW θ)).continuousAt.comp
      (f := fun u : Fin N → ℝ => (t,deformedAngles τ p m u))
      (continuous_const.prodMk hw).continuousAt
  exact ((preferredContourMatrix_contDiff (N := N) τ p m hp hm).continuous.matrix_det.mul hd).div_const _

def fullPopulationIntegral (negative : Bool) (n : ℕ) (τ : ℝ)
    (η p m : ℝ → ℝ) (t : ℂ) : ℂ :=
  weightedContourIntegral negative n τ p m (preferredFullPopulationWeight η p m) t

def lowerPopulationIntegral (negative : Bool) (n : ℕ) (τ : ℝ)
    (η p m : ℝ → ℝ) (t : ℂ) : ℂ :=
  weightedContourIntegral negative n τ p m (preferredLowerWeight η p m) t

def upperPopulationIntegral (negative : Bool) (n : ℕ) (τ : ℝ)
    (η p m : ℝ → ℝ) (t : ℂ) : ℂ :=
  weightedContourIntegral negative n τ p m (preferredUpperPopulationWeight η p m) t

theorem lower_upper_population_equal (negative : Bool) (n : ℕ) (τ : ℝ)
    (η p : ℝ → ℝ) (hpp : Function.Periodic p (2*Real.pi)) (t : ℂ) :
    lowerPopulationIntegral negative n τ η p (fun x => p (-x)) t =
      upperPopulationIntegral negative n τ η p (fun x => p (-x)) t := by
  unfold lowerPopulationIntegral upperPopulationIntegral weightedContourIntegral
  rw [← angularBox_integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    rw [bareContourDensity_constrained_reflect negative n τ p hpp]
    congr 1
    have hm : Function.Periodic (fun x => p (-x)) (2*Real.pi) := by
      intro x
      change p (-(x+2*Real.pi))=p (-x)
      rw [show -(x+2*Real.pi)= -x-2*Real.pi by ring]
      exact hpp.sub_eq _
    have hw : preferredLowerWeight η p (fun x => p (-x)) (constrainedAngles negative n (-θ)) =
        preferredLowerWeight η p (fun x => p (-x)) (-(constrainedAngles negative n θ)) := by
      unfold preferredLowerWeight occupancy
      simp_rw [signed_reflection_periodic_data negative θ p hpp,
        signed_reflection_periodic_data negative θ (fun x => p (-x)) hm]
      rfl
    rw [hw,preferred_population_weight_reflect]

theorem complete_population_partition (negative : Bool) (n : ℕ) {t : ℂ}
    (ht : 1<‖t‖) (hS : 0<(temperatureTrace t).im) (τ : ℝ) (hτ : 0≤τ)
    (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hpp : Function.Periodic p (2*Real.pi))
    (hp0 : ∀ x,0≤p x) (hps : ∀ x,Real.sin x≤0 → p x=0)
    (η : ℝ → ℝ) (hη : Continuous η) :
    signedCoefficient negative (n+1) t =
      fullPopulationIntegral negative n τ η p (fun x => p (-x)) t +
        2*lowerPopulationIntegral negative n τ η p (fun x => p (-x)) t := by
  let m := fun x => p (-x)
  have hm : ContDiff ℝ ∞ m := hp.comp contDiff_neg
  have hmp : Function.Periodic m (2*Real.pi) := by
    intro x
    change p (-(x+2*Real.pi))=p (-x)
    rw [show -(x+2*Real.pi)= -x-2*Real.pi by ring]
    exact hpp.sub_eq _
  have hm0 : ∀ x,0≤m x := fun x => hp0 (-x)
  have hms : ∀ x,0≤Real.sin x → m x=0 := by
    intro x hx
    exact hps (-x) (by simpa only [Real.sin_neg,neg_nonpos] using hx)
  have hW (θ : Fin (n+1) → ℝ) (i) : OffRealSegment
      (t+t⁻¹-Complex.cos (deformedAngles τ p m θ i)) := by
    have hh := homotopy_complexW_im_pos hS hτ (by norm_num : (0:ℝ)≤1)
      p m θ hp0 hm0 hps hms i
    rw [Geometry.homotopyRoot_eq_exp_angle,complexW_exp_I] at hh
    exact Or.inl (by simpa [Geometry.homotopyAngles,deformedAngles,temperatureTrace] using hh.ne')
  let f := fun θ : Fin n → ℝ => bareContourDensity negative τ p m t (constrainedAngles negative n θ)
  let F := fun θ : Fin n → ℝ => (preferredFullPopulationWeight η p m (constrainedAngles negative n θ):ℂ)*f θ
  let L := fun θ : Fin n → ℝ => (preferredLowerWeight η p m (constrainedAngles negative n θ):ℂ)*f θ
  let U := fun θ : Fin n → ℝ => (preferredUpperPopulationWeight η p m (constrainedAngles negative n θ):ℂ)*f θ
  have hf : Continuous f := (bareContourDensity_continuous negative (by omega) τ p m hp hm t
    (norm_ne_zero_iff.mp (by linarith)) hW).comp (constrainedAngles_continuous negative n)
  have hp' := hp.continuous
  have hm' := hm.continuous
  have hc := constrainedAngles_continuous negative n
  have hF : Continuous F := by
    dsimp only [F]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredFullPopulationWeight fullWeight occupancy
    fun_prop
  have hL : Continuous L := by
    dsimp only [L]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredLowerWeight lowerWeight occupancy
    fun_prop
  have hU : Continuous U := by
    dsimp only [U]
    apply Continuous.mul _ hf
    apply Complex.continuous_ofReal.comp
    unfold preferredUpperPopulationWeight upperWeight occupancy
    fun_prop
  have hiF := continuous_integrableOn_angularBox hF
  have hiL := continuous_integrableOn_angularBox hL
  have hiU := continuous_integrableOn_angularBox hU
  have hpoint (θ : Fin n → ℝ) : (F θ+L θ)+U θ=f θ := by
    dsimp only [F,L,U]
    rw [← add_mul,← add_mul,← Complex.ofReal_add,← Complex.ofReal_add,
      preferred_population_weight_sum,Complex.ofReal_one,one_mul]
  rw [signedCoefficient_eq_wholeContour negative n ht hS τ hτ p m hp hm hpp hmp hp0 hm0 hps hms]
  change (∫ θ in angularBox n, (1:ℂ)*f θ) = _
  simp only [one_mul]
  have hi : (∫ θ in angularBox n,f θ)=
      (∫ θ in angularBox n,F θ)+(∫ θ in angularBox n,L θ)+(∫ θ in angularBox n,U θ) := by
    calc
      _ = ∫ θ in angularBox n,(F θ+L θ)+U θ :=
        integral_congr_ae (Filter.Eventually.of_forall fun θ => (hpoint θ).symm)
      _ = (∫ θ in angularBox n,F θ+L θ)+(∫ θ in angularBox n,U θ) :=
        integral_add (hiF.add hiL) hiU
      _ = _ := congrArg (fun z => z+∫ θ in angularBox n,U θ) (integral_add hiF hiL)
  rw [hi]
  change fullPopulationIntegral negative n τ η p m t + lowerPopulationIntegral negative n τ η p m t +
    upperPopulationIntegral negative n τ η p m t = _
  rw [← lower_upper_population_equal negative n τ η p hpp t]
  ring

end
end IsingBulk.HT22.Physical
