import IsingBulk.HT22.Physical.Symmetries
import IsingBulk.HT22.Geometry.WholeTorus
import IsingBulk.HT22.Algebra.OddBordered
import IsingBulk.Preferred22.Transport

/-!
# The literal signed density on the complete balanced contour

There is a single bare density, with the full occupancy Jacobian and the
original factorial and N−1 dimensional Haar normalizer. Localization weights
are real functions of the original angular variables and are inserted only
by `weightedContourIntegral`, after whole-torus deformation.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open Set Filter MeasureTheory
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped Topology BigOperators ContDiff

/-- Gauge-free density in the actual circle coordinates. -/
def rootFreeSignedDensity (negative : Bool) {N : ℕ} (t : ℂ) (y : Fin N → ℂ) : ℂ :=
  let z := fun i => IsingBulk.Preferred22.physicalRoot (IsingBulk.Preferred22.complexW t (y i))
  ((1+constraintSign negative*∏ i,z i)/(1-constraintSign negative*∏ i,z i)) *
    (∏ i,oneBody (z i)) * canceledPairProduct z y

theorem rootFreeSignedDensity_eq_complexSignedDensity (negative : Bool) {N : ℕ}
    (t : ℂ) (w : Fin N → ℂ) :
    rootFreeSignedDensity negative t (fun i => Complex.exp (Complex.I*w i)) =
      complexSignedDensity negative (t,w) := by
  simp only [rootFreeSignedDensity,complexSignedDensity,complexRoot,complexAngle,
    IsingBulk.Preferred22.complexW_exp_I,IsingBulk.Preferred22.temperatureTrace]

/-- The complete source density; no population or branch weight is hidden. -/
def bareContourDensity (negative : Bool) {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (IsingBulk.Preferred22.preferredContourMatrix τ p m θ).det *
    complexSignedDensity negative (t,IsingBulk.Preferred22.deformedAngles τ p m θ) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

/-- A real smooth weight on the original complete affine angular constraint. -/
def weightedContourIntegral (negative : Bool) (n : ℕ) (τ : ℝ) (p m : ℝ → ℝ)
    (weight : (Fin (n+1) → ℝ) → ℝ) (t : ℂ) : ℂ :=
  ∫ q in IsingBulk.Preferred22.angularBox n,
    (weight (constrainedAngles negative n q):ℂ) *
      bareContourDensity negative τ p m t (constrainedAngles negative n q)

theorem signedAngularDensity_continuous (negative : Bool) {N : ℕ}
    (hN : 0<N) {t : ℂ} (ht : 1<‖t‖) :
    Continuous (signedAngularDensity negative (N := N) t) := by
  have hc : Continuous (fun θ : Fin N → ℝ =>
      complexSignedDensity negative (t,fun i => (θ i:ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (complexSignedDensity_analyticAt negative hN ht θ).continuousAt.comp
      (f := fun u : Fin N → ℝ => (t,fun i => (u i:ℂ)))
      (continuous_const.prodMk (continuous_pi fun i =>
        Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt
  simpa only [complexSignedDensity_real] using hc

/-- Exact conversion from the published iterated integral on [0,2π] to the
centered fundamental box, including the signed affine last angle. -/
theorem signedCoefficient_eq_angularBox (negative : Bool) (n : ℕ)
    {t : ℂ} (ht : 1<‖t‖) :
    signedCoefficient negative (n+1) t =
      ((n+1).factorial:ℂ)⁻¹ * ((2*Real.pi:ℂ)⁻¹)^n *
        ∫ q in IsingBulk.Preferred22.angularBox n,
          signedAngularDensity negative t (constrainedAngles negative n q) := by
  let f := fun q => signedAngularDensity negative t (constrainedAngles negative n q)
  have hc : Continuous f :=
    (signedAngularDensity_continuous negative (by omega) ht).comp
      (constrainedAngles_continuous negative n)
  have hp := signedConstrainedDensity_periodic negative n t
  rw [signedCoefficient_succ,signedCoefficientWithAngles]
  congr 1
  rw [IsingBulk.Preferred22.angularBox_integral_eq_shifted_box,
    multiAngleIntegral_eq_box _ _ hc]
  exact (angleBox_integral_shift n f hc hp (fun _ => -Real.pi)).symm

/-- The manuscript's rational pair is exactly the pair used in the literal
physical coefficient; this includes all collision zeros. -/
theorem physicalPair_eq_canceledPair (a b z w : ℂ) :
    Algebra.physicalPair a b z w = canceledPair a b z w := by
  rw [Algebra.physicalPair_eq]
  unfold canceledPair
  ring

/-- Genuine odd bordered determinant identity on the deformed physical
sheet. It is not the old LT even determinant. -/
theorem complexSignedDensity_eq_bordered (negative : Bool) (n : ℕ)
    (t : ℂ) (w : Fin (2*n+1) → ℂ)
    (hW : ∀ i, 0<(IsingBulk.Preferred22.temperatureTrace t-Complex.cos (w i)).im) :
    complexSignedDensity negative (t,w) =
      let y := fun i => Complex.exp (Complex.I*w i)
      let z := fun i => IsingBulk.Preferred22.physicalRoot
        (IsingBulk.Preferred22.temperatureTrace t-Complex.cos (w i))
      ((1+constraintSign negative*∏ i,z i)/(1-constraintSign negative*∏ i,z i)) *
        (Algebra.constantBorderFirst y z).det * (∏ i,oneBody (z i)) := by
  let y := fun i => Complex.exp (Complex.I*w i)
  let z := fun i => IsingBulk.Preferred22.physicalRoot
    (IsingBulk.Preferred22.temperatureTrace t-Complex.cos (w i))
  have hz (i) : ‖z i‖<1 :=
    IsingBulk.Preferred22.physicalRoot_inside (Or.inl (hW i).ne')
  have hc (i) : y i+(y i)⁻¹+z i+(z i)⁻¹ =
      2*IsingBulk.Preferred22.temperatureTrace t := by
    have hy := IsingBulk.Preferred22.complexW_exp_I t (w i)
    have ht := IsingBulk.Preferred22.physicalRoot_trace
      (IsingBulk.Preferred22.temperatureTrace t-Complex.cos (w i))
    change z i+(z i)⁻¹ = _ at ht
    unfold IsingBulk.Preferred22.complexW at hy
    change _ - (y i+(y i)⁻¹)/2 = _ at hy
    linear_combination ht - 2*hy
  have hd := Algebra.odd_constantBorderFirst_determinant n
    (IsingBulk.Preferred22.temperatureTrace t) y z
    (fun _ => Complex.exp_ne_zero _) (fun _ => IsingBulk.Preferred22.physicalRoot_ne_zero _)
    hc (fun i j _ => one_sub_mul_ne_zero_of_norm_lt_one (hz i) (hz j))
  have hp : (Algebra.constantBorderFirst y z).det = canceledPairProduct z y := by
    rw [hd]
    unfold canceledPairProduct
    apply Finset.prod_congr rfl
    intro i _
    simp only [physicalPair_eq_canceledPair]
    apply Finset.prod_congr
    · ext j
      simp
    · intro j _
      rfl
  change _ = ((1+constraintSign negative*∏ i,z i)/(1-constraintSign negative*∏ i,z i)) *
    (Algebra.constantBorderFirst y z).det * (∏ i,oneBody (z i))
  rw [hp]
  change _ * _ * canceledPairProduct z y = _
  simp only [complexRoot,IsingBulk.Preferred22.temperatureTrace] at *
  dsimp only [z,IsingBulk.Preferred22.temperatureTrace]
  ring

theorem bareContourDensity_eq_bordered (negative : Bool) (n : ℕ)
    (τ : ℝ) (p m : ℝ → ℝ) (t : ℂ) (θ : Fin (2*n+1) → ℝ)
    (hW : ∀ i, 0<(IsingBulk.Preferred22.temperatureTrace t-
      Complex.cos (IsingBulk.Preferred22.deformedAngles τ p m θ i)).im) :
    bareContourDensity negative τ p m t θ =
      let w := IsingBulk.Preferred22.deformedAngles τ p m θ
      let y := fun i => Complex.exp (Complex.I*w i)
      let z := fun i => IsingBulk.Preferred22.physicalRoot
        (IsingBulk.Preferred22.temperatureTrace t-Complex.cos (w i))
      (IsingBulk.Preferred22.preferredContourMatrix τ p m θ).det *
        ((1+constraintSign negative*∏ i,z i)/(1-constraintSign negative*∏ i,z i)) *
        (Algebra.constantBorderFirst y z).det * (∏ i,oneBody (z i)) /
        (((2*n+1).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n)) := by
  unfold bareContourDensity
  rw [complexSignedDensity_eq_bordered negative n t _ hW]
  simp only [Nat.add_sub_cancel]
  ring

end
end IsingBulk.HT22.Physical
