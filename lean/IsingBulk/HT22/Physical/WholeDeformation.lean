import IsingBulk.HT22.Physical.ContourDensity
import IsingBulk.HT22.Physical.SignedJacobian

/-! Actual signed odd density on the complete balanced constrained torus.
No localization weight enters the Stokes homotopy. -/
namespace IsingBulk.HT22.Physical
noncomputable section
open Set Filter MeasureTheory IsingBulk.HT22.Geometry
open IsingBulk.Preferred22 IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem rootFreeSignedDensity_differentiableAt (negative : Bool) {N : ℕ}
    (hN : 0<N) (t : ℂ) (y : Fin N → ℂ) (hy : ∀ i,y i≠0)
    (hW : ∀ i,0<(complexW t (y i)).im) :
    DifferentiableAt ℂ (rootFreeSignedDensity negative t) y := by
  let z := fun x : Fin N → ℂ => fun i => physicalRoot (complexW t (x i))
  have hzi : ∀ i,‖z y i‖<1 := fun i => physicalRoot_inside (Or.inl (hW i).ne')
  have dz (i) : DifferentiableAt ℂ (fun x => z x i) y := by
    have di : DifferentiableAt ℂ (fun x : Fin N → ℂ => x i) y := differentiableAt_apply i y
    have dw : DifferentiableAt ℂ (fun x : Fin N → ℂ => complexW t (x i)) y := by
      unfold complexW
      convert! (differentiableAt_const (temperatureTrace t)).sub
        ((di.add (di.inv (hy i))).mul_const (2⁻¹:ℂ)) using 1
    exact (physicalRoot_differentiableAt_upper (hW i)).comp y dw
  have dZ : DifferentiableAt ℂ (fun x => ∏ i,z x i) y :=
    (HasFDerivAt.finsetProd (fun i _ => (dz i).hasFDerivAt)).differentiableAt
  have db : DifferentiableAt ℂ (fun x => ∏ i,Physical.oneBody (z x i)) y := by
    simp_rw [oneBody_eq_rational]
    apply HasFDerivAt.differentiableAt
    apply HasFDerivAt.finsetProd
    intro i _
    exact (contour_differentiable_div ((dz i).const_mul 2)
      ((differentiableAt_const (1:ℂ)).sub ((dz i).pow 2))
      (by simpa [pow_two] using complex_pair_gap (hzi i) (hzi i))).hasFDerivAt
  have dp (i j) : DifferentiableAt ℂ
      (fun x => IsingBulk.Tail.canceledPair (x i) (x j) (z x i) (z x j)) y := by
    exact contour_differentiable_div
      (((((differentiableAt_apply i y).sub (differentiableAt_apply j y)).pow 2).neg.mul
        (dz i)).mul (dz j))
      (((differentiableAt_apply i y).mul (differentiableAt_apply j y)).mul
        (((differentiableAt_const (1:ℂ)).sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy i) (hy j))
        (pow_ne_zero 2 (complex_pair_gap (hzi i) (hzi j))))
  have dP : DifferentiableAt ℂ
      (fun x => IsingBulk.Tail.canceledPairProduct (z x) x) y := by
    apply HasFDerivAt.differentiableAt
    apply HasFDerivAt.finsetProd
    intro i _
    apply HasFDerivAt.finsetProd
    intro j _
    exact (dp i j).hasFDerivAt
  exact ((contour_differentiable_div
    ((differentiableAt_const (1:ℂ)).add (dZ.const_mul (constraintSign negative)))
    ((differentiableAt_const (1:ℂ)).sub (dZ.const_mul (constraintSign negative)))
    (unit_signed_product_gap hN _ (fun _ => physicalRoot_ne_zero _) hzi _
      (constraintSign_norm negative))).mul db).mul dP

def signedLogDensity (negative : Bool) (n : ℕ) (t : ℂ) (x : Fin n → ℂ) : ℂ :=
  rootFreeSignedDensity negative t
    (fun i => Complex.exp (signedComplex (constraintAngle negative) x i))

theorem signedLogDensity_differentiableAt (negative : Bool) (n : ℕ) (t : ℂ)
    (x : Fin n → ℂ)
    (hW : ∀ i,0<(complexW t (Complex.exp (signedComplex (constraintAngle negative) x i))).im) :
    DifferentiableAt ℂ (signedLogDensity negative n t) x := by
  have he : DifferentiableAt ℂ
      (fun y => fun i => Complex.exp (signedComplex (constraintAngle negative) y i)) x := by
    apply differentiableAt_pi.mpr
    intro i
    exact Complex.differentiableAt_exp.comp x
      (((contDiff_apply ℂ ℂ i).comp (signedComplex_contDiff n _)).differentiable (by simp) x)
  exact (rootFreeSignedDensity_differentiableAt negative (by omega) t _
    (fun _ => Complex.exp_ne_zero _) hW).comp x he

theorem signedLogDensity_periodic (negative : Bool) (n : ℕ) (t : ℂ)
    (x : Fin n → ℂ) (q : Fin n) :
    signedLogDensity negative n t (x+Pi.single q (2*Real.pi*Complex.I)) =
      signedLogDensity negative n t x := by
  unfold signedLogDensity
  rw [signed_exp_periodic]

def signedDeformedCoefficient (negative : Bool) (n : ℕ) (t : ℂ)
    (τ lam : ℝ) (p m : ℝ → ℝ) : ℂ :=
  (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)⁻¹ *
    ∫ θ in angularBox n,
      rootFreeSignedDensity negative t
        (homotopyRoot τ lam p m (Geometry.signedAngles (constraintAngle negative) θ)) *
      (signedDerivativeJacobian (constraintAngle negative) τ lam p m θ).det

theorem signedDeformedCoefficient_eq_cap (negative : Bool) (n : ℕ) (s : ℂ) (τ lam : ℝ) (p m : ℝ → ℝ) :
    signedDeformedCoefficient negative n s τ lam p m =
      ((Nat.factorial (n+1):ℂ)*(2*Real.pi:ℂ)^n)⁻¹ * (-Complex.I)^n *
        cylinderCapIntegral (signedPullback (signedLogDensity negative n s) (constraintAngle negative) τ p m)
          (homotopyBoxLower n) (homotopyBoxUpper n) lam := by
  unfold signedDeformedCoefficient
  have hbox : angularBox n =ᵐ[volume]
      Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi) :=
    Measure.univ_pi_Ioc_ae_eq_Icc
  rw [setIntegral_congr_set hbox]
  unfold cylinderCapIntegral
  simp only [homotopyBoxLower, homotopyBoxUpper, Function.comp_def,
    Fin.succAbove_zero, Fin.cons_succ, Fin.insertNth_zero', Fin.removeNth_zero,
    signedPullback, densityForm_chainPullback]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  have he : signedLogDensity negative n s (signedParameterHomotopy (constraintAngle negative) τ p m (Fin.cons lam θ)) =
      rootFreeSignedDensity negative s (homotopyRoot τ lam p m (Geometry.signedAngles (constraintAngle negative) θ)) := by
    unfold signedLogDensity signedParameterHomotopy
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    funext i
    exact signed_exp_homotopy (constraintAngle negative) τ lam p m θ i
  rw [he]
  let J : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    fderiv ℝ (signedParameterHomotopy (constraintAngle negative) τ p m) (Fin.cons lam θ) (Pi.single i.succ 1) j
  have hm : signedDerivativeJacobian (constraintAngle negative) τ lam p m θ = (-Complex.I) • J := rfl
  rw [hm, Matrix.det_smul]
  simp only [Fintype.card_fin]
  change _ = _ * (_ * J.det)
  ring



theorem signedDeformedCoefficient_zero (negative : Bool) (n : ℕ) {t : ℂ}
    (ht : 1<‖t‖) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    signedDeformedCoefficient negative n t τ 0 p m = signedCoefficient negative (n+1) t := by
  rw [signedCoefficient_eq_angularBox negative n ht]
  unfold signedDeformedCoefficient
  have hj (θ : Fin n → ℝ) :
      (signedDerivativeJacobian (constraintAngle negative) τ 0 p m θ).det=1 := by
    rw [signedDerivativeJacobian_det_eq_full _ _ _ _ _ hp hm]
    have he : fullAngularJacobian τ 0 p m (Geometry.signedAngles (constraintAngle negative) θ) = 1 := by
      ext i j
      simp [fullAngularJacobian,Matrix.one_apply]
    rw [he,Matrix.det_one]
  simp_rw [hj,mul_one]
  have hd (θ : Fin n → ℝ) : rootFreeSignedDensity negative t
      (homotopyRoot τ 0 p m (Geometry.signedAngles (constraintAngle negative) θ)) =
      signedAngularDensity negative t (constrainedAngles negative n θ) := by
    have he : homotopyRoot τ 0 p m (Geometry.signedAngles (constraintAngle negative) θ) =
        fun i => Complex.exp (Complex.I*(constrainedAngles negative n θ i:ℂ)) := by
      funext i
      simp [homotopyRoot,Geometry.signedAngles,constrainedAngles]
    rw [he,rootFreeSignedDensity_eq_complexSignedDensity,complexSignedDensity_real]
  simp_rw [hd]
  simp [← inv_pow, mul_comm, mul_assoc]

theorem signedCoefficient_eq_deformed (negative : Bool) (n : ℕ) {t : ℂ}
    (ht : 1<‖t‖) (hS : 0<(temperatureTrace t).im) (τ : ℝ) (hτ : 0≤τ)
    (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp0 : ∀ x,0≤p x) (hm0 : ∀ x,0≤m x)
    (hps : ∀ x,Real.sin x≤0 → p x=0) (hms : ∀ x,0≤Real.sin x → m x=0) :
    signedCoefficient negative (n+1) t = signedDeformedCoefficient negative n t τ 1 p m := by
  have hc := signed_whole_homotopy_caps n (signedLogDensity negative n t)
    (constraintAngle negative) τ p m hp hm hpp hmp (signedLogDensity_periodic negative n t)
    (by
      intro x hx
      apply signedLogDensity_differentiableAt
      intro i
      rw [show x = Fin.cons (x 0) (fun j => x j.succ) from (Fin.cons_self_tail x).symm]
      change 0<(complexW t (Complex.exp (signedComplex (constraintAngle negative)
        (signedFreeLogHomotopy (constraintAngle negative) τ (x 0) p m (fun j => x j.succ)) i))).im
      rw [signed_exp_homotopy]
      exact homotopy_complexW_im_pos hS hτ (by simpa [homotopyBoxLower] using hx.1 0)
        p m _ hp0 hm0 hps hms i)
  rw [← signedDeformedCoefficient_zero negative n ht τ p m hp hm,
    signedDeformedCoefficient_eq_cap,signedDeformedCoefficient_eq_cap,hc]


theorem signedDeformedCoefficient_one (negative : Bool) (n : ℕ) (t : ℂ)
    (τ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    signedDeformedCoefficient negative n t τ 1 p m =
      weightedContourIntegral negative n τ p m (fun _ => 1) t := by
  unfold signedDeformedCoefficient weightedContourIntegral bareContourDensity
  simp only [Complex.ofReal_one,one_mul,Nat.add_sub_cancel]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro θ _
  dsimp only
  rw [signedDerivativeJacobian_det_eq_full _ _ _ _ _ hp hm]
  have hj : fullAngularJacobian τ 1 p m (Geometry.signedAngles (constraintAngle negative) θ) =
      preferredContourMatrix τ p m (constrainedAngles negative n θ) := by
    ext i j
    simp only [fullAngularJacobian,preferredContourMatrix,Complex.ofReal_one,mul_one]
    rfl
  have hr : homotopyRoot τ 1 p m (Geometry.signedAngles (constraintAngle negative) θ) =
      fun i => Complex.exp (Complex.I*deformedAngles τ p m (constrainedAngles negative n θ) i) := by
    funext i
    rw [homotopyRoot_eq_exp_angle]
    simp only [homotopyAngles,deformedAngles,Complex.ofReal_one,mul_one]
    rfl
  rw [hj,hr,rootFreeSignedDensity_eq_complexSignedDensity]
  ring

/-- F001 whole constrained homotopy with the exact full source density,
normalizer and both signs. The only weight is the constant one. -/
theorem signedCoefficient_eq_wholeContour (negative : Bool) (n : ℕ) {t : ℂ}
    (ht : 1<‖t‖) (hS : 0<(temperatureTrace t).im) (τ : ℝ) (hτ : 0≤τ)
    (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp0 : ∀ x,0≤p x) (hm0 : ∀ x,0≤m x)
    (hps : ∀ x,Real.sin x≤0 → p x=0) (hms : ∀ x,0≤Real.sin x → m x=0) :
    signedCoefficient negative (n+1) t =
      weightedContourIntegral negative n τ p m (fun _ => 1) t := by
  rw [signedCoefficient_eq_deformed negative n ht hS τ hτ p m hp hm hpp hmp hp0 hm0 hps hms,
    signedDeformedCoefficient_one negative n t τ p m hp hm]

end
end IsingBulk.HT22.Physical
