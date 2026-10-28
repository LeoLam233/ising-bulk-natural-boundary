import IsingBulk.HT22.Physical.Holomorphy
import IsingBulk.Preferred22.EvenSymmetry
import IsingBulk.Anisotropic.RegularEdges.AngularNumeratorBridge
import IsingBulk.Joint.FormFactors.ParticleConjugation

/-!
# Literal signed angular symmetries

Reflection in real angles is an equality, not complex conjugation. Parameter
conjugation is proved separately. Whole-box translations preserve the actual
constrained Haar measure; parity changes the auxiliary signed constraint.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Filter
open scoped Topology
open scoped BigOperators

local notation "angle" => IsingBulk.Preferred22.angleRoot

theorem limitingAngle_eq_preferred (q : ℝ) : limitingAngle q = angle q := by
  simp only [limitingAngle, IsingBulk.Preferred22.angleRoot, mul_comm]

theorem angularRoot_reflect (t : ℂ) (q : ℝ) : angularRoot t (-q) = angularRoot t q := by
  simp only [angularRoot, IsingBulk.Preferred22.angularW, Real.cos_neg]

theorem angularRoot_conj {t : ℂ} (ht : 1 < ‖t‖) (q : ℝ) :
    angularRoot (star t) q = star (angularRoot t q) := by
  have hW : IsingBulk.Preferred22.angularW (star t) q =
      star (IsingBulk.Preferred22.angularW t q) := by
    simp only [IsingBulk.Preferred22.angularW, IsingBulk.Preferred22.temperatureTrace,
      star_add, star_inv₀, star_sub, Complex.star_def, Complex.conj_ofReal]
  unfold angularRoot
  rw [hW, IsingBulk.Preferred22.physicalRoot_conj
    (IsingBulk.Preferred22.angularW_off_segment ht q)]

theorem oneBody_conj (z : ℂ) : oneBody (star z) = star (oneBody z) := by
  simp [oneBody]

theorem oneBody_neg (z : ℂ) : oneBody (-z) = -oneBody z := by
  rw [oneBody_eq_rational, oneBody_eq_rational]
  simp only [neg_sq, mul_neg, neg_div]

theorem canceledPair_unit_reflect (a b : ℝ) (z w : ℂ) :
    canceledPair (limitingAngle (-a)) (limitingAngle (-b)) z w =
      canceledPair (limitingAngle a) (limitingAngle b) z w := by
  simp_rw [IsingBulk.Anisotropic.RegularEdges.canceledPair_unit_eq_angularRootPair]
  unfold IsingBulk.Anisotropic.RegularEdges.angularRootPair
  have hd : ((-a:ℝ):ℂ)-((-b:ℝ):ℂ) = -((a:ℂ)-(b:ℂ)) := by push_cast; ring
  rw [hd, neg_div, Complex.sin_neg, neg_sq]

theorem canceledPair_unit_conj (a b : ℝ) (z w : ℂ) :
    canceledPair (limitingAngle a) (limitingAngle b) (star z) (star w) =
      star (canceledPair (limitingAngle a) (limitingAngle b) z w) := by
  simp_rw [IsingBulk.Anisotropic.RegularEdges.canceledPair_unit_eq_angularRootPair]
  unfold IsingBulk.Anisotropic.RegularEdges.angularRootPair
  have hr : Complex.sin (((a:ℂ)-(b:ℂ))/2) = (Real.sin ((a-b)/2):ℂ) := by
    push_cast
    rfl
  rw [hr]
  simp only [star_div₀, star_mul', star_pow, star_sub, star_one, star_ofNat,
    Complex.star_def, Complex.conj_ofReal]

theorem canceledPair_neg_all (a b z w : ℂ) :
    canceledPair (-a) (-b) (-z) (-w) = canceledPair a b z w := by
  unfold canceledPair
  have he : -a-(-b) = -(a-b) := by ring
  rw [he, neg_sq]
  simp only [mul_neg, neg_mul, neg_neg]

/-- Reflection preserves the actual full density exactly, at either sign. -/
theorem signedAngularDensity_reflect (negative : Bool) {N : ℕ}
    (t : ℂ) (phi : Fin N → ℝ) :
    signedAngularDensity negative t (fun i => -phi i) =
      signedAngularDensity negative t phi := by
  simp only [signedAngularDensity, angularRoot_reflect, canceledPairProduct,
    canceledPair_unit_reflect]

/-- Conjugation is a distinct symmetry; the real sine-square angular numerator
means that no conjugation of the integration measure is required. -/
theorem signedAngularDensity_conj (negative : Bool) {N : ℕ}
    {t : ℂ} (ht : 1 < ‖t‖) (phi : Fin N → ℝ) :
    signedAngularDensity negative (star t) phi =
      star (signedAngularDensity negative t phi) := by
  have hs : star (constraintSign negative) = constraintSign negative := by
    cases negative <;> simp [constraintSign]
  simp only [signedAngularDensity, angularRoot_conj ht, oneBody_conj,
    canceledPairProduct, canceledPair_unit_conj, star_prod, star_mul,
    star_div₀, star_add, star_sub, star_one, hs]
  ring

theorem signedCoefficientWithAngles_conj (negative : Bool) (n : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) :
    signedCoefficientWithAngles negative n (star t) =
      star (signedCoefficientWithAngles negative n t) := by
  simp_rw [signedCoefficientWithAngles, signedAngularDensity_conj negative ht]
  rw [← IsingBulk.Joint.FormFactors.multiAngleIntegral_star]
  simp only [star_mul', star_inv₀, star_pow, star_natCast, star_ofNat,
    Complex.star_def, Complex.conj_ofReal]

theorem signedCoefficient_conj (negative : Bool) (N : ℕ)
    {t : ℂ} (ht : 1 < ‖t‖) :
    signedCoefficient negative N (star t) = star (signedCoefficient negative N t) := by
  cases N with
  | zero => simp [signedCoefficient]
  | succ n => simpa only [signedCoefficient_succ] using
      signedCoefficientWithAngles_conj negative n ht

/-- Equality depends only on the actual circle angles, including at collisions. -/
theorem signedAngularDensity_congr_angles (negative : Bool) {N : ℕ}
    (t : ℂ) (phi psi : Fin N → ℝ) (h : ∀ i, angle (phi i) = angle (psi i)) :
    signedAngularDensity negative t phi = signedAngularDensity negative t psi := by
  have hy : (fun i => limitingAngle (phi i)) = (fun i => limitingAngle (psi i)) := by
    funext i
    simpa only [limitingAngle_eq_preferred] using h i
  have hz : (fun i => angularRoot t (phi i)) = (fun i => angularRoot t (psi i)) := by
    funext i
    simp only [angularRoot, IsingBulk.Preferred22.angularW,
      IsingBulk.Preferred22.cos_eq_of_angleRoot_eq (h i)]
  have hzi (i : Fin N) := congrFun hz i
  simp only [signedAngularDensity, hy, hzi]

theorem signedConstrainedDensity_periodic (negative : Bool) (n : ℕ) (t : ℂ) :
    CoordinatePeriodic n (fun q =>
      signedAngularDensity negative t (constrainedAngles negative n q)) := by
  intro q i
  apply signedAngularDensity_congr_angles
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [constrainedAngles, Fin.snoc_last]
    have hsum : (∑ j, Function.update q i (q i+2*Real.pi) j) =
        (∑ j, q j)+2*Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) q]
      ring
    rw [hsum, show constraintAngle negative - ((∑ j, q j)+2*Real.pi) =
      (constraintAngle negative-∑ j, q j)-2*Real.pi by ring]
    exact IsingBulk.Preferred22.angleRoot_periodic.sub_eq _
  · simp only [constrainedAngles, Fin.snoc_castSucc]
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact IsingBulk.Preferred22.angleRoot_periodic _
    · rw [Function.update_of_ne hji]

/-- The pi-rotation negates every angular root and flips the signed resolvent
for odd particle count. The complete pair product itself is unchanged. -/
theorem signedAngularDensity_neg_of_angles (negative : Bool) {N : ℕ}
    (hN : Odd N) {t : ℂ} (ht : 1 < ‖t‖)
    (phi psi : Fin N → ℝ) (hy : ∀ i, angle (psi i) = -angle (phi i)) :
    signedAngularDensity (!negative) (-t) psi = -signedAngularDensity negative t phi := by
  have hw (i : Fin N) : IsingBulk.Preferred22.angularW (-t) (psi i) =
      -IsingBulk.Preferred22.angularW t (phi i) := by
    have hc : Real.cos (psi i) = -Real.cos (phi i) := by
      rw [IsingBulk.Preferred22.cos_eq_of_angleRoot_eq
        ((hy i).trans (IsingBulk.Preferred22.angleRoot_add_pi (phi i)).symm),
        Real.cos_add_pi]
    simp only [IsingBulk.Preferred22.angularW, IsingBulk.Preferred22.temperatureTrace,
      inv_neg, hc, Complex.ofReal_neg]
    ring
  have hz (i : Fin N) : angularRoot (-t) (psi i) = -angularRoot t (phi i) := by
    unfold angularRoot
    rw [hw, IsingBulk.Preferred22.physicalRoot_neg
      (IsingBulk.Preferred22.angularW_off_segment ht (phi i))]
  have hy' (i : Fin N) : limitingAngle (psi i) = -limitingAngle (phi i) := by
    simpa only [limitingAngle_eq_preferred] using hy i
  simp only [signedAngularDensity, hz, hy', canceledPairProduct,
    canceledPair_neg_all, oneBody_neg, Finset.prod_neg,
    Finset.card_univ, Fintype.card_fin, hN.neg_one_pow, neg_one_mul]
  cases negative <;> norm_num [constraintSign]

/-- The free-angle pi translation maps the positive torus to the negative
one at odd N. The dependent angle differs by an exact integer period. -/
theorem constrainedAngles_add_pi_positive_to_negative {n : ℕ}
    (hn : Odd (n+1)) (q : Fin n → ℝ) :
    ∀ j, angle (constrainedAngles false n (fun i => q i+Real.pi) j) =
      -angle (constrainedAngles true n q j) := by
  obtain ⟨m, hm⟩ := hn
  have hnR : (n:ℝ) = 2*(m:ℝ) := by exact_mod_cast (show n=2*m by omega)
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [constrainedAngles, Fin.snoc_last, constraintAngle, Bool.false_eq_true, ↓reduceIte,
      zero_sub, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show -((∑ i, q i)+(n:ℝ)*Real.pi) =
      (-(∑ i, q i))-(m:ℝ)*(2*Real.pi) by rw [hnR]; ring,
      IsingBulk.Preferred22.angleRoot_periodic.sub_nat_mul_eq]
    rw [show Real.pi-(∑ i, q i) = (-(∑ i, q i))+Real.pi by ring,
      IsingBulk.Preferred22.angleRoot_add_pi, neg_neg]
  · simp only [constrainedAngles, Fin.snoc_castSucc,
      IsingBulk.Preferred22.angleRoot_add_pi]

/-- The exact complete integral transforms with the full affine constraint and
Haar measure preserved. No weighted or truncated contour is substituted. -/
theorem signedCoefficient_odd_neg {n : ℕ} (hn : Odd (n+1))
    {t : ℂ} (ht : 1 < ‖t‖) :
    signedCoefficient false (n+1) (-t) = -signedCoefficient true (n+1) t := by
  simp only [signedCoefficient_succ, signedCoefficientWithAngles]
  let F : (Fin n → ℝ) → ℂ := fun q =>
    signedAngularDensity false (-t) (constrainedAngles false n q)
  have hshift := multiAngleIntegral_shift n F
    (signedConstrainedDensity_periodic false n (-t)) (fun _ => Real.pi)
  have he (q : Fin n → ℝ) : F (fun i => q i+Real.pi) =
      -signedAngularDensity true t (constrainedAngles true n q) :=
    signedAngularDensity_neg_of_angles true hn ht _ _
      (constrainedAngles_add_pi_positive_to_negative hn q)
  change _ * multiAngleIntegral n F = _
  rw [← hshift]
  simp_rw [he]
  rw [show (fun q : Fin n → ℝ => -signedAngularDensity true t (constrainedAngles true n q)) =
    (fun q => (-1:ℂ)*signedAngularDensity true t (constrainedAngles true n q)) by funext q; ring,
    physical_multiAngleIntegral_const_mul]
  ring

/-- The same odd signed relation, explicitly indexed by particle number. -/
theorem coefficient_odd_neg (n : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    coefficient (2*n+1) (-t) = -signedCoefficient true (2*n+1) t :=
  signedCoefficient_odd_neg (by exact ⟨n, by omega⟩) ht

/-- Reflection of the independent variables preserves either affine constraint
modulo its exact period. It never introduces complex conjugation. -/
theorem constrainedDensity_reflect (negative : Bool) (n : ℕ) (t : ℂ)
    (q : Fin n → ℝ) :
    signedAngularDensity negative t (constrainedAngles negative n (fun i => -q i)) =
      signedAngularDensity negative t (constrainedAngles negative n q) := by
  calc
    _ = signedAngularDensity negative t (fun i => -constrainedAngles negative n q i) := by
      apply signedAngularDensity_congr_angles
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [constrainedAngles, Fin.snoc_last, Finset.sum_neg_distrib, sub_neg_eq_add]
        cases negative
        · simp [constraintAngle]
        · simp only [constraintAngle, ↓reduceIte]
          rw [show Real.pi+∑ j, q j = (-(Real.pi-∑ j, q j))+2*Real.pi by ring]
          exact IsingBulk.Preferred22.angleRoot_periodic _
      · simp only [constrainedAngles, Fin.snoc_castSucc]
    _ = _ := signedAngularDensity_reflect negative t _

/-- Derivatives respect the actual signed negation identity on a neighborhood,
with the sign coming from the chain rule rather than an evenness assumption. -/
theorem negativeCoefficient_iteratedDeriv (n j : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    iteratedDeriv j (signedCoefficient true (2*n+1)) t =
      -((-1:ℂ)^j * iteratedDeriv j (coefficient (2*n+1)) (-t)) := by
  have he : signedCoefficient true (2*n+1) =ᶠ[nhds t]
      (fun z => -coefficient (2*n+1) (-z)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with z hz
    have h := coefficient_odd_neg n hz
    linear_combination h
  rw [he.iteratedDeriv_eq j, iteratedDeriv_fun_neg, iteratedDeriv_comp_neg]
  simp only [smul_eq_mul]

/-- Reflection has unit modulus, uniformly in the derivative and particle orders. -/
theorem negativeCoefficient_iteratedDeriv_norm (n j : ℕ) {t : ℂ}
    (ht : 1 < ‖t‖) :
    ‖iteratedDeriv j (signedCoefficient true (2*n+1)) t‖ =
      ‖iteratedDeriv j (coefficient (2*n+1)) (-t)‖ := by
  rw [negativeCoefficient_iteratedDeriv n j ht]
  simp only [norm_neg, norm_mul, norm_pow, norm_one, one_pow, one_mul]

end
end IsingBulk.HT22.Physical
