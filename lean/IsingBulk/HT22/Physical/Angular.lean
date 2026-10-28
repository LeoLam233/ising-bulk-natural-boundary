import IsingBulk.HT.Contour.PhysicalAngularPairs
import IsingBulk.Preferred22.PhysicalAnalytic

/-!
# Literal constrained angular coefficients for HT22

The integral below uses exactly `N - 1` independent angles for `N > 0`,
normalized Haar measure, the complete rational squared pair product, and
`(z⁻¹-z)/2` for `sinh gamma`. Its root is the established unique root
inside the unit disk, selected from two explicit reciprocal quadratic roots.
The generic Preferred22 root construction is shared; its LT even-particle
determinant coefficient and boundary proof are not reused.

Only the real restriction is proved in this module. In particular, defining
this integral does not assert exterior holomorphy or normal convergence.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

/-- The globally constructed small root, with analyticity already established
on the complement of the physical slit. No square root is reset along a path. -/
def angularRoot (t : ℂ) (theta : ℝ) : ℂ :=
  IsingBulk.Preferred22.physicalRoot (IsingBulk.Preferred22.angularW t theta)

/-- F001's literal one-body factor, without choosing a logarithm. -/
def oneBody (z : ℂ) : ℂ := ((z⁻¹-z)/2)⁻¹

/-- The two auxiliary constraints have total angle zero and pi. -/
def constraintAngle (negative : Bool) : ℝ := if negative then Real.pi else 0

def constraintSign (negative : Bool) : ℂ := if negative then -1 else 1

def constrainedAngles (negative : Bool) (n : ℕ) (phi : Fin n → ℝ) :
    Fin (n+1) → ℝ :=
  Fin.snoc (α := fun _ : Fin (n+1) => ℝ) phi
    (constraintAngle negative - ∑ i, phi i)

/-- The complete signed angular density before inserting any localization. -/
def signedAngularDensity (negative : Bool) {N : ℕ} (t : ℂ)
    (phi : Fin N → ℝ) : ℂ :=
  let z := fun i => angularRoot t (phi i)
  let y := fun i => limitingAngle (phi i)
  ((1 + constraintSign negative * ∏ i, z i) /
    (1 - constraintSign negative * ∏ i, z i)) *
    (∏ i, oneBody (z i)) * canceledPairProduct z y

/-- `n` is the independent-angle count; the particle count is `n+1`. -/
def signedCoefficientWithAngles (negative : Bool) (n : ℕ) (t : ℂ) : ℂ :=
  ((n+1).factorial : ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun phi =>
      signedAngularDensity negative t (constrainedAngles negative n phi))

/-- The F001 coefficient indexed by particle number. There is no zero-particle term. -/
def signedCoefficient (negative : Bool) (N : ℕ) (t : ℂ) : ℂ :=
  if N = 0 then 0 else signedCoefficientWithAngles negative (N-1) t

def coefficient (N : ℕ) (t : ℂ) : ℂ := signedCoefficient false N t

theorem signedCoefficient_succ (negative : Bool) (n : ℕ) (t : ℂ) :
    signedCoefficient negative (n+1) t = signedCoefficientWithAngles negative n t := by
  simp [signedCoefficient]

theorem constrainedAngles_positive (n : ℕ) (phi : Fin n → ℝ) :
    constrainedAngles false n phi = physicalDependentAngles n phi := by
  simp [constrainedAngles, constraintAngle, physicalDependentAngles]

/-- The dependent angle imposes the exact affine constraint, before mod 2pi. -/
theorem constrainedAngles_total (negative : Bool) (n : ℕ) (phi : Fin n → ℝ) :
    (∑ i, constrainedAngles negative n phi i) = constraintAngle negative := by
  simp only [constrainedAngles, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem angularW_eq_sourceW (t : ℂ) (phi : ℝ) :
    IsingBulk.Preferred22.angularW t phi = sourceW t (limitingAngle phi) := by
  unfold IsingBulk.Preferred22.angularW IsingBulk.Preferred22.temperatureTrace sourceW sourceS
  rw [limitingAngle_trace]
  ring

theorem angularRoot_eq_rightRoot_real {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    angularRoot (t:ℂ) phi = rightRoot (t:ℂ) (limitingAngle phi) := by
  have hW : 1 < (sourceW (t:ℂ) (limitingAngle phi)).re := by
    rw [sourceW_real_unit_angle]
    exact physical_W_gt_one ht phi
  unfold angularRoot
  rw [angularW_eq_sourceW]
  exact quadratic_root_unique
    (IsingBulk.Preferred22.physicalRoot_quadratic _)
    (compactLeftRoot_quadratic _)
    (IsingBulk.Preferred22.physicalRoot_inside (Or.inr (hW.trans_le (le_abs_self _))))
    (compactLeftRoot_norm_lt_one hW)

theorem angularRoot_real {t : ℝ} (ht : 1 < t) (phi : ℝ) :
    angularRoot (t:ℂ) phi = (physicalRoot t phi:ℂ) := by
  rw [angularRoot_eq_rightRoot_real ht, rightRoot_real_unit_angle ht]

theorem angularRoot_norm_lt_one {t : ℂ} (ht : 1 < ‖t‖) (phi : ℝ) :
    ‖angularRoot t phi‖ < 1 :=
  IsingBulk.Preferred22.physicalRoot_inside
    (IsingBulk.Preferred22.angularW_off_segment ht phi)

theorem angularRoot_ne_zero (t : ℂ) (phi : ℝ) : angularRoot t phi ≠ 0 :=
  IsingBulk.Preferred22.physicalRoot_ne_zero _

theorem angularRoot_analyticAt {t : ℂ} (ht : 1 < ‖t‖) (phi : ℝ) :
    AnalyticAt ℂ (fun z => angularRoot z phi) t :=
  IsingBulk.Preferred22.angularRoot_analyticAt ht phi

theorem oneBody_physicalRoot (t phi : ℝ) :
    oneBody (physicalRoot t phi:ℂ) = ((Real.sinh (physicalGamma t phi))⁻¹:ℝ) := by
  have he : (((physicalRoot t phi:ℂ)⁻¹ - (physicalRoot t phi:ℂ))/2) =
      (Real.sinh (physicalGamma t phi):ℂ) := by
    have hr : ((physicalRoot t phi)⁻¹ - physicalRoot t phi)/2 =
        Real.sinh (physicalGamma t phi) := by
      simp only [physicalRoot, Real.sinh_eq, Real.exp_neg, inv_inv]
    exact_mod_cast hr
  rw [oneBody, he]
  simp only [Complex.ofReal_inv]

theorem signedAngularDensity_positive_real {N : ℕ} {t : ℝ}
    (ht : 1 < t) (phi : Fin N → ℝ) :
    signedAngularDensity false (t:ℂ) phi =
      ((physicalAngularWeight t phi *
        ((1+physicalZ t phi)/(1-physicalZ t phi)):ℝ):ℂ) := by
  unfold signedAngularDensity
  dsimp only
  simp_rw [angularRoot_eq_rightRoot_real ht]
  rw [physical_canceledPairProduct ht]
  simp only [rightRoot_real_unit_angle ht, oneBody_physicalRoot]
  simp only [constraintSign, Bool.false_eq_true, ↓reduceIte,
    one_mul, physicalAngularWeight, physicalZ, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_prod, Complex.ofReal_inv]
  ring

theorem signedAngularDensity_negative_real {N : ℕ} {t : ℝ}
    (ht : 1 < t) (phi : Fin N → ℝ) :
    signedAngularDensity true (t:ℂ) phi =
      ((physicalAngularWeight t phi *
        ((1-physicalZ t phi)/(1+physicalZ t phi)):ℝ):ℂ) := by
  unfold signedAngularDensity
  dsimp only
  simp_rw [angularRoot_eq_rightRoot_real ht]
  rw [physical_canceledPairProduct ht]
  simp only [rightRoot_real_unit_angle ht, oneBody_physicalRoot]
  simp only [constraintSign, ↓reduceIte, neg_one_mul, sub_neg_eq_add,
    physicalAngularWeight, physicalZ, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_prod, Complex.ofReal_inv]
  ring

theorem constrainedAngles_zero (negative : Bool) :
    constrainedAngles negative 0 (Fin.elim0 : Fin 0 → ℝ) =
      fun _ : Fin 1 => constraintAngle negative := by
  funext i
  have hi : i = Fin.last 0 := Fin.ext (by omega)
  subst i
  dsimp only [constrainedAngles]
  rw [Fin.snoc_last]
  simp

theorem physicalPairProduct_one (t phi : ℝ) :
    physicalPairProduct t (fun _ : Fin 1 => phi) = 1 := by
  have hempty (i : Fin 1) : Finset.univ.filter (fun j : Fin 1 => i < j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hji : j = i := Fin.ext (by omega)
    exact (lt_irrefl i) (by simpa only [hji] using (Finset.mem_filter.mp hj).2)
  simp only [physicalPairProduct, hempty, Finset.prod_empty, Finset.prod_const_one]

/-- Scalar check for the auxiliary negative constraint, independent of logarithms. -/
theorem physical_one_particle_scalar_minus {gamma : ℝ} (hg : 0 < gamma) :
    (Real.sinh gamma)⁻¹ * ((1-Real.exp (-gamma))/(1+Real.exp (-gamma))) =
      (Real.cosh gamma+1)⁻¹ := by
  have hE : Real.exp gamma ≠ 0 := (Real.exp_pos _).ne'
  have hs : Real.sinh gamma ≠ 0 := (Real.sinh_pos_iff.mpr hg).ne'
  have hz : 1+Real.exp (-gamma) ≠ 0 := by positivity
  have hc : Real.cosh gamma+1 ≠ 0 := by
    have h := Real.one_le_cosh gamma
    positivity
  have hid : (Real.cosh gamma+1)*(1-Real.exp (-gamma)) =
      Real.sinh gamma*(1+Real.exp (-gamma)) := by
    rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
    field_simp
    ring
  field_simp
  nlinarith [hid]

/-- The signed N=1 formulas use different constraints, not a sign-switched
physical observable. The negative constraint has its angle fixed at pi. -/
theorem signedCoefficient_one_negative_real {t : ℝ} (ht : 1 < t) :
    signedCoefficient true 1 (t:ℂ) = ((t+t⁻¹+2)⁻¹:ℝ) := by
  have hscalar := physical_one_particle_scalar_minus (physicalGamma_pos ht Real.pi)
  rw [physicalGamma_cosh ht, Real.cos_pi] at hscalar
  have he : t+t⁻¹-(-1)+1 = t+t⁻¹+2 := by ring
  rw [he] at hscalar
  change signedCoefficient true (0+1) (t:ℂ) = _
  rw [signedCoefficient_succ]
  simp only [signedCoefficientWithAngles, Nat.zero_add, Nat.factorial_one,
    Nat.cast_one, inv_one, pow_zero, one_mul, multiAngleIntegral,
    constrainedAngles_zero, constraintAngle, ↓reduceIte,
    signedAngularDensity_negative_real ht]
  simpa only [physicalAngularWeight, physicalZ, physicalPairProduct_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.zero_add, pow_one,
    mul_one, physicalRoot] using congrArg (fun x : ℝ => (x:ℂ)) hscalar

/-- Exact real-temperature coefficient identity, with the N−1 count exposed. -/
theorem coefficient_eq_published_succ (n : ℕ) {t : ℝ} (ht : 1 < t) :
    coefficient (n+1) (t:ℂ) = physicalAngularCoefficient n t := by
  rw [coefficient, signedCoefficient_succ]
  unfold signedCoefficientWithAngles physicalAngularCoefficient
  congr 2
  funext phi
  rw [constrainedAngles_positive, signedAngularDensity_positive_real ht]

theorem coefficient_eq_published {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    coefficient N (t:ℂ) = physicalAngularCoefficient (N-1) t := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa using coefficient_eq_published_succ n ht

/-- Every positive odd particle count is mapped to exactly 2n independent angles. -/
theorem coefficient_odd_eq_published (n : ℕ) {t : ℝ} (ht : 1 < t) :
    coefficient (2*n+1) (t:ℂ) = physicalAngularCoefficient (2*n) t :=
  coefficient_eq_published_succ (2*n) ht

theorem coefficient_one_real {t : ℝ} (ht : 1 < t) :
    coefficient 1 (t:ℂ) = ((t+t⁻¹-2)⁻¹:ℝ) := by
  exact (coefficient_eq_published_succ 0 ht).trans (physicalAngularCoefficient_one ht)

end
end IsingBulk.HT22.Physical
