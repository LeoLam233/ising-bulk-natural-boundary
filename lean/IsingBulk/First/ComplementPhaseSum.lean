import IsingBulk.First.ComplementPhase

/-! The actual finite auxiliary phase and its normalized simplex separator. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι]

def sourcePhaseSum {N : ℕ} (r : ℝ) (s : ℂ) (x y : Fin N → ℂ)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ) (u : DoubleAngularVector N) : ℂ :=
  ∑ i, (η i : ℂ) * sourceAngularExponent r s x y (J i) u

/-- The complete actual finite phase is smooth in the angular variables. -/
theorem sourcePhaseSum_contDiff {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ) :
    ContDiff ℝ ∞ (sourcePhaseSum r s x y J η) := by
  unfold sourcePhaseSum
  exact ContDiff.sum (fun i _ => contDiff_const.mul
    (sourceAngularExponent_contDiff r hr s x y hx hy (J i)))

/-- Imaginary angular derivative of the actual phase is the positive weighted
sum of actual damped source gradients. -/
theorem sourcePhaseSum_direction_im {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ) (u e : DoubleAngularVector N) :
    (phaseDirection e (sourcePhaseSum r s x y J η) u).im =
      ∑ i, η i * angularDot e
        (dampedSingularVector r (torusShift x u.1) (torusShift y u.2) (J i)) := by
  have hx0 (i) : x i ≠ 0 := by intro h; have hh := hx i; simp [h] at hh
  have hy0 (i) : y i ≠ 0 := by intro h; have hh := hy i; simp [h] at hh
  have hg (i) := sourceAngularExponent_contDiff r hr s x y hx0 hy0 (J i)
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hg i).differentiable (by simp) u).hasFDerivAt.const_mul (η i : ℂ))
  have he := congrArg (fun L : DoubleAngularVector N →L[ℝ] ℂ => (L e).im) hd.fderiv
  have he' : (phaseDirection e (sourcePhaseSum r s x y J η) u).im =
      ∑ i, η i * (phaseDirection e (sourceAngularExponent r s x y (J i)) u).im := by
    unfold phaseDirection sourcePhaseSum
    simpa [smul_apply, Complex.mul_im] using he
  rw [he']
  simp_rw [sourceAngularExponent_direction_im r hr s x y hx hy]

/-- A normalized nonnegative auxiliary vector turns the common active-factor
separator into a quantitative nonzero direction for the actual total phase. -/
theorem sourcePhaseSum_direction_margin {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ)
    (hη : ∀ i, 0 ≤ η i) (hηsum : ∑ i, η i = 1)
    (u e : DoubleAngularVector N) {δ : ℝ}
    (hsep : ∀ i, δ ≤ angularDot e
      (dampedSingularVector r (torusShift x u.1) (torusShift y u.2) (J i))) :
    δ ≤ (phaseDirection e (sourcePhaseSum r s x y J η) u).im := by
  rw [sourcePhaseSum_direction_im r hr s x y hx hy]
  calc
    δ = ∑ i, η i * δ := by rw [← Finset.sum_mul, hηsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hsep i) (hη i))

/-- The denominator of the integration-by-parts operator is proved nonzero. -/
theorem sourcePhaseSum_direction_ne_zero {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ)
    (hη : ∀ i, 0 ≤ η i) (hηsum : ∑ i, η i = 1)
    (u e : DoubleAngularVector N) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, δ ≤ angularDot e
      (dampedSingularVector r (torusShift x u.1) (torusShift y u.2) (J i))) :
    phaseDirection e (sourcePhaseSum r s x y J η) u ≠ 0 := by
  intro hz
  have h := sourcePhaseSum_direction_margin r hr s x y hx hy J η hη hηsum u e hsep
  rw [hz, Complex.zero_im] at h
  linarith

/-- The real-part damping of the complete phase is inherited from the actual
factors and nonnegative auxiliary variables. -/
theorem sourcePhaseSum_re_nonpositive {N : ℕ} (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hmargin : r⁻¹-r < (sourceS s).im)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ) (hη : ∀ i, 0 ≤ η i)
    (u : DoubleAngularVector N) : (sourcePhaseSum r s x y J η u).re ≤ 0 := by
  change Complex.reCLM (∑ i, (η i : ℂ) * sourceAngularExponent r s x y (J i) u) ≤ 0
  rw [map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hη i)
    (singularFactorExponent_re_negative hN hr hr1 hmargin x y hx hy u (J i) 1).le)

/-- Normalizing an auxiliary ray is an exact algebraic equality of phases. -/
theorem sourcePhaseSum_normalize {N : ℕ} (r : ℝ) (s : ℂ) (x y : Fin N → ℂ)
    (J : ι → SingularFactorIndex N) (ξ : ι → ℝ) (R : ℝ) (hR : R ≠ 0)
    (u : DoubleAngularVector N) :
    sourcePhaseSum r s x y J ξ u =
      (R : ℂ) * sourcePhaseSum r s x y J (fun i => ξ i / R) u := by
  unfold sourcePhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  field_simp [hRc]

end
end IsingBulk.First
