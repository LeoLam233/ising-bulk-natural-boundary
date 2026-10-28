import IsingBulk.HT22.Physical.Angular
import IsingBulk.First.CompactIntegralHolomorphic
import IsingBulk.First.AngularFubini
import IsingBulk.HT.Contour.SignedKernel

/-!
# Exterior holomorphy of each actual signed F001 angular coefficient

The full constrained integral is used, including the dependent last angle.
This proof shares only generic root, compact integration, and denominator-gap
lemmas. It does not identify the odd density with the LT22 even determinant.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology BigOperators

theorem oneBody_eq_rational (z : ℂ) : oneBody z = 2*z/(1-z^2) := by
  by_cases hz : z = 0
  · simp [oneBody, hz]
  · have he : (z⁻¹-z)/2 = (1-z^2)/(2*z) := by
      field_simp
    rw [oneBody, he, inv_div]

theorem constraintSign_norm (negative : Bool) : ‖constraintSign negative‖ = 1 := by
  cases negative <;> simp [constraintSign]

def complexAngle (q : ℂ) : ℂ := Complex.exp (Complex.I*q)

def complexRoot (t q : ℂ) : ℂ :=
  IsingBulk.Preferred22.physicalRoot (t+t⁻¹-Complex.cos q)

def complexSignedDensity (negative : Bool) {N : ℕ}
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  let z := fun i => complexRoot p.1 (p.2 i)
  let y := fun i => complexAngle (p.2 i)
  ((1 + constraintSign negative * ∏ i, z i) /
    (1 - constraintSign negative * ∏ i, z i)) *
    (∏ i, oneBody (z i)) * canceledPairProduct z y

theorem complexRoot_real (t : ℂ) (q : ℝ) :
    complexRoot t (q:ℂ) = angularRoot t q := by
  simp only [complexRoot, angularRoot, IsingBulk.Preferred22.angularW,
    IsingBulk.Preferred22.temperatureTrace, ← Complex.ofReal_cos]

theorem complexSignedDensity_real (negative : Bool) {N : ℕ}
    (t : ℂ) (phi : Fin N → ℝ) :
    complexSignedDensity negative (t, fun i => (phi i:ℂ)) =
      signedAngularDensity negative t phi := by
  simp only [complexSignedDensity, signedAngularDensity, complexRoot_real,
    complexAngle, limitingAngle, mul_comm]

/-- Joint complex analyticity is proved for every actual angle, without a
branch reset. Strict |z|<1 proves all complete-product denominator gaps. -/
theorem complexSignedDensity_analyticAt (negative : Bool) {N : ℕ}
    (hN : 0 < N) {t : ℂ} (ht : 1 < ‖t‖) (phi : Fin N → ℝ) :
    AnalyticAt ℂ (@complexSignedDensity negative N) (t, fun i => (phi i:ℂ)) := by
  let p : ℂ × (Fin N → ℂ) := (t, fun i => (phi i:ℂ))
  have ht0 : t ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dy (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexAngle (x.2 i)) p :=
    (analyticAt_const.mul (dq i)).cexp
  have dS : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.1+x.1⁻¹) p :=
    analyticAt_fst.add (analyticAt_fst.inv ht0)
  have dz (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexRoot x.1 (x.2 i)) p := by
    have dW := dS.sub (Complex.analyticAt_cos.comp (dq i))
    exact (IsingBulk.Preferred22.physicalRoot_analyticAt
      (IsingBulk.Preferred22.angularW_off_segment ht (phi i))).comp_of_eq dW
      (by simp only [p, IsingBulk.Preferred22.angularW,
        IsingBulk.Preferred22.temperatureTrace, ← Complex.ofReal_cos])
  have hn (i : Fin N) : ‖complexRoot p.1 (p.2 i)‖ < 1 := by
    simpa only [p, complexRoot_real] using angularRoot_norm_lt_one ht (phi i)
  have hpair (i j : Fin N) : 1-complexRoot p.1 (p.2 i)*complexRoot p.1 (p.2 j) ≠ 0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-constraintSign negative*∏ i, complexRoot p.1 (p.2 i) ≠ 0 :=
    signed_product_gap_ne_zero hN _ (constraintSign_norm negative) _ hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dz i)
  have dbody : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      ∏ i, oneBody (complexRoot x.1 (x.2 i))) p := by
    simp_rw [oneBody_eq_rational]
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dz i)).div (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPair (complexAngle (x.2 i)) (complexAngle (x.2 j))
        (complexRoot x.1 (x.2 i)) (complexRoot x.1 (x.2 j))) p := by
    exact (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
        (pow_ne_zero 2 (hpair i j)))
  have dpairs : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPairProduct (fun i => complexRoot x.1 (x.2 i))
        (fun i => complexAngle (x.2 i))) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i < j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  exact (((analyticAt_const.add (analyticAt_const.mul dZ)).div
    (analyticAt_const.sub (analyticAt_const.mul dZ)) hZ).mul dbody).mul dpairs

theorem constrainedAngles_continuous (negative : Bool) (n : ℕ) :
    Continuous (constrainedAngles negative n) := by
  unfold constrainedAngles
  fun_prop

/-- Finite coefficient holomorphy: this is not a statement about the infinite sum. -/
theorem signedCoefficientWithAngles_analyticAt (negative : Bool) (n : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) :
    AnalyticAt ℂ (signedCoefficientWithAngles negative n) t := by
  let U : Set ℂ := {t | 1 < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun q i => (constrainedAngles negative n q i:ℂ)
  have hpsi : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (constrainedAngles_continuous negative n)))
  let F := @complexSignedDensity negative (n+1)
  have hF : ∀ w∈U, ∀ q∈angleBox n, AnalyticAt ℂ F (w,psi q) := by
    intro w hw q _
    exact complexSignedDensity_analyticAt negative (by omega) hw (constrainedAngles negative n q)
  have hcont (w : ℂ) (hw : w∈U) : Continuous (fun q => F (w,psi q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (complexSignedDensity_analyticAt negative (by omega) hw
      (constrainedAngles negative n q)).continuousAt.comp
      (f := fun q => (w,psi q)) (continuous_const.prodMk hpsi).continuousAt
  have ha := compact_analytic_shape_integral_analyticAt
    (μ := volume) (K := angleBox n) isCompact_Icc hU F psi hpsi
    (fun _ => (1:ℂ)) continuous_const hF ht
  have hb : AnalyticAt ℂ (fun w => multiAngleIntegral n (fun q => F (w,psi q))) t := by
    apply ha.congr
    filter_upwards [hU.mem_nhds ht] with w hw
    simpa only [one_mul] using
      (multiAngleIntegral_eq_box n (fun q => F (w,psi q)) (hcont w hw)).symm
  have he : (fun w => multiAngleIntegral n (fun q => F (w,psi q))) =
      fun w => multiAngleIntegral n (fun q =>
        signedAngularDensity negative w (constrainedAngles negative n q)) := by
    funext w
    congr 1
    funext q
    exact complexSignedDensity_real negative w (constrainedAngles negative n q)
  rw [he] at hb
  exact analyticAt_const.mul hb

theorem signedCoefficient_analyticAt (negative : Bool) (N : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) : AnalyticAt ℂ (signedCoefficient negative N) t := by
  cases N with
  | zero =>
    change AnalyticAt ℂ (fun _ : ℂ => 0) t
    exact analyticAt_const
  | succ n =>
    have he : signedCoefficient negative (n+1) = signedCoefficientWithAngles negative n :=
      funext (signedCoefficient_succ negative n)
    rw [he]
    exact signedCoefficientWithAngles_analyticAt negative n ht

theorem coefficient_analyticAt (N : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    AnalyticAt ℂ (coefficient N) t :=
  signedCoefficient_analyticAt false N ht

end
end IsingBulk.HT22.Physical
