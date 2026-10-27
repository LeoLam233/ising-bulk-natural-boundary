import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.SqrtDeriv
import IsingBulk.Analysis.BranchAttenuation
import IsingBulk.Analysis.BranchUpper
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import IsingBulk.Preferred22.Physical

/-!
# LT22 Preferred: the explicit limiting inverse coordinate

The function below is the real limiting form of formula (6.1), with
`v=q+w_B`.  We derive its first and second derivatives from the actual
arccosine formula.  Positivity is then a theorem, not a curvature premise.
Extension to a common complex neighborhood and uniform mixed jets are
not asserted here.
-/

namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology

def rightInverse (S v : ℝ) : ℝ :=
  v/2 - Real.arccos (S/(2*Real.cos (v/2)))

def inverseDiscriminant (S v : ℝ) : ℝ :=
  4*(Real.cos (v/2))^2-S^2

def rightInverseSlope (S v : ℝ) : ℝ :=
  1/2 + S*Real.sin (v/2) /
    (2*Real.cos (v/2)*Real.sqrt (inverseDiscriminant S v))

def rightInverseCurvature (S v : ℝ) : ℝ :=
  S / (4*(Real.cos (v/2))^2*Real.sqrt (inverseDiscriminant S v)) +
    S*(Real.sin (v/2))^2 / (Real.sqrt (inverseDiscriminant S v))^3

theorem inverseDiscriminant_arccos_margin {S c : ℝ} (hc : 0 < c)
    (hD : 0 < 4*c^2-S^2) : |S/(2*c)| < 1 := by
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 2*c)).2
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < 2*c)).2
    nlinarith

theorem inverse_sqrt_rescaling {S c : ℝ} (hc : 0 < c)
    (hD : 0 < 4*c^2-S^2) :
    Real.sqrt (1-(S/(2*c))^2) = Real.sqrt (4*c^2-S^2)/(2*c) := by
  have hm := inverseDiscriminant_arccos_margin hc hD
  have hm' := abs_lt.mp hm
  have hA : 0 ≤ 1-(S/(2*c))^2 := by nlinarith
  have ha := Real.sq_sqrt hA
  have hr := Real.sq_sqrt hD.le
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hden : (2*c)^2 ≠ 0 := by positivity
  have hpoly : (2*c*Real.sqrt (1-(S/(2*c))^2))^2 =
      (Real.sqrt (4*c^2-S^2))^2 := by
    rw [mul_pow, ha, hr]
    field_simp
    ; ring
  have hp : 0 ≤ 2*c*Real.sqrt (1-(S/(2*c))^2) := by positivity
  have hq := Real.sqrt_nonneg (4*c^2-S^2)
  have heq : 2*c*Real.sqrt (1-(S/(2*c))^2) = Real.sqrt (4*c^2-S^2) := by
    nlinarith
  apply (eq_div_iff (by positivity : 2*c ≠ 0)).2
  nlinarith [heq]

/-- The first derivative of the literal formula (6.1). -/
theorem rightInverse_hasDerivAt (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    HasDerivAt (rightInverse S) (rightInverseSlope S v) v := by
  have hh : HasDerivAt (fun t : ℝ => t/2) (1/2) v := by
    simpa using (hasDerivAt_id v).div_const 2
  have hcos := (Real.hasDerivAt_cos (v/2)).comp v hh
  have hden : HasDerivAt (fun t : ℝ => 2*Real.cos (t/2))
      (-Real.sin (v/2)) v := by
    convert! hcos.const_mul 2 using 1 ; ring
  have hc0 : Real.cos (v/2) ≠ 0 := ne_of_gt hc
  have harg : HasDerivAt (fun t : ℝ => S/(2*Real.cos (t/2)))
      (S*Real.sin (v/2)/(4*(Real.cos (v/2))^2)) v := by
    convert! (hasDerivAt_const v S).div hden (by positivity) using 1
    ring
  have hm := abs_lt.mp (inverseDiscriminant_arccos_margin hc hD)
  have harc := (Real.hasDerivAt_arccos (by linarith : S/(2*Real.cos (v/2)) ≠ -1)
    (by linarith : S/(2*Real.cos (v/2)) ≠ 1)).comp v harg
  have hcalc := hh.sub harc
  convert! hcalc using 1
  unfold rightInverseSlope
  rw [inverse_sqrt_rescaling hc hD]
  have hr : Real.sqrt (inverseDiscriminant S v) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hD)
  dsimp [inverseDiscriminant] at hr ⊢
  field_simp
  ; ring

theorem rightInverse_deriv (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    deriv (rightInverse S) v = rightInverseSlope S v :=
  (rightInverse_hasDerivAt S v hc hD).deriv

theorem inverse_curvature_algebra {S c t r : ℝ} (hc : c ≠ 0) (hr : r ≠ 0)
    (hunit : t^2+c^2=1) :
    ((S*(c/2))*(2*c*r) - (S*t)*(-t*r-4*c^2*t/r))/(2*c*r)^2 =
      S/(4*c^2*r)+S*t^2/r^3 := by
  field_simp
  linear_combination 4*S*r^2*hunit

/-- The derivative of the explicit slope is precisely (6.2). -/
theorem rightInverseSlope_hasDerivAt (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    HasDerivAt (rightInverseSlope S) (rightInverseCurvature S v) v := by
  have hh : HasDerivAt (fun t : ℝ => t/2) (1/2) v := by
    simpa using (hasDerivAt_id v).div_const 2
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (t/2))
      (-Real.sin (v/2)/2) v := by
    convert! (Real.hasDerivAt_cos (v/2)).comp v hh using 1 ; ring
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (t/2))
      (Real.cos (v/2)/2) v := by
    convert! (Real.hasDerivAt_sin (v/2)).comp v hh using 1 ; ring
  have hdisc : HasDerivAt (inverseDiscriminant S)
      (-4*Real.cos (v/2)*Real.sin (v/2)) v := by
    convert! ((hcos.pow 2).const_mul 4).sub_const (S^2) using 1 ; ring
  have hroot : HasDerivAt (fun t : ℝ => Real.sqrt (inverseDiscriminant S t))
      (-2*Real.cos (v/2)*Real.sin (v/2)/Real.sqrt (inverseDiscriminant S v)) v := by
    convert! (Real.hasDerivAt_sqrt (ne_of_gt hD)).comp v hdisc using 1
    ring
  have hprod : HasDerivAt
      (fun t : ℝ => 2*Real.cos (t/2)*Real.sqrt (inverseDiscriminant S t))
      (-Real.sin (v/2)*Real.sqrt (inverseDiscriminant S v) -
       4*(Real.cos (v/2))^2*Real.sin (v/2)/Real.sqrt (inverseDiscriminant S v)) v := by
    convert! (hcos.const_mul 2).mul hroot using 1 ; ring
  have hr : Real.sqrt (inverseDiscriminant S v) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hD)
  have hc0 : Real.cos (v/2) ≠ 0 := ne_of_gt hc
  have hquot := (hsin.const_mul S).div hprod (by positivity)
  have hfull := hquot.const_add (1/2)
  convert! hfull using 1
  unfold rightInverseCurvature
  exact (inverse_curvature_algebra hc0 hr (Real.sin_sq_add_cos_sq (v/2))).symm

theorem rightInverse_second_hasDerivAt (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    HasDerivAt (deriv (rightInverse S)) (rightInverseCurvature S v) v := by
  have hccont : Continuous (fun t : ℝ => Real.cos (t/2)) := by fun_prop
  have hDcont : Continuous (inverseDiscriminant S) := by
    unfold inverseDiscriminant
    fun_prop
  have hcnear : ∀ᶠ t in 𝓝 v, 0 < Real.cos (t/2) :=
    hccont.continuousAt.eventually (lt_mem_nhds hc)
  have hDnear : ∀ᶠ t in 𝓝 v, 0 < inverseDiscriminant S t :=
    hDcont.continuousAt.eventually (lt_mem_nhds hD)
  have heq : deriv (rightInverse S) =ᶠ[𝓝 v] rightInverseSlope S := by
    filter_upwards [hcnear, hDnear] with t hct hDt
    exact rightInverse_deriv S t hct hDt
  exact (rightInverseSlope_hasDerivAt S v hc hD).congr_of_eventuallyEq heq

theorem rightInverse_second_deriv (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    deriv (deriv (rightInverse S)) v = rightInverseCurvature S v :=
  (rightInverse_second_hasDerivAt S v hc hD).deriv

/-- Strict right-side convexity follows from the actual inverse formula. -/
theorem rightInverse_strict_curvature (S v : ℝ) (hS : 0 < S)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    0 < deriv (deriv (rightInverse S)) v := by
  rw [rightInverse_second_deriv S v hc hD]
  unfold rightInverseCurvature
  have hr : 0 < Real.sqrt (inverseDiscriminant S v) := Real.sqrt_pos.mpr hD
  exact add_pos_of_pos_of_nonneg (by positivity) (by positivity)

/-- In fact the real limiting interval admits the explicit uniform margin
`S/8`, before choosing any complex-neighborhood margin. -/
theorem rightInverse_uniform_curvature (S v : ℝ) (hS : 0 < S)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    S/8 ≤ deriv (deriv (rightInverse S)) v := by
  rw [rightInverse_second_deriv S v hc hD]
  have hr : 0 < Real.sqrt (inverseDiscriminant S v) := Real.sqrt_pos.mpr hD
  have hc2 : (Real.cos (v/2))^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (v/2), sq_nonneg (Real.sin (v/2))]
  have hdisc : inverseDiscriminant S v ≤ 4 := by
    unfold inverseDiscriminant
    nlinarith [sq_nonneg S]
  have hr2 : Real.sqrt (inverseDiscriminant S v) ≤ 2 := by
    nlinarith [Real.sq_sqrt hD.le]
  have hdenpos : 0 < 4*(Real.cos (v/2))^2*Real.sqrt (inverseDiscriminant S v) := by
    positivity
  have hden : 4*(Real.cos (v/2))^2*Real.sqrt (inverseDiscriminant S v) ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_right hc2 hr.le
    nlinarith
  have hfirst : S/8 ≤
      S/(4*(Real.cos (v/2))^2*Real.sqrt (inverseDiscriminant S v)) := by
    apply (le_div_iff₀ hdenpos).2
    nlinarith
  unfold rightInverseCurvature
  exact le_trans hfirst (le_add_of_nonneg_right (by positivity))

def realMovingInverse (S wB q : ℝ) : ℝ := rightInverse S (q+wB)

theorem rightInverse_at_lower_branch (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    rightInverse (1+Real.cos b) (-b) = -b := by
  have hc : 0 < Real.cos (b/2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcos : 1+Real.cos b = 2*(Real.cos (b/2))^2 := by
    have hh := Real.cos_two_mul (b/2)
    rw [show 2*(b/2)=b by ring] at hh
    nlinarith
  have harg : (1+Real.cos b)/(2*Real.cos (-b/2)) = Real.cos (b/2) := by
    rw [show -b/2 = -(b/2) by ring, Real.cos_neg, hcos]
    field_simp
  unfold rightInverse
  rw [harg, Real.arccos_cos (by linarith) (by linarith)]
  ring

theorem realMovingInverse_at_zero (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    realMovingInverse (1+Real.cos b) (-b) 0 = -b := by
  simpa [realMovingInverse] using rightInverse_at_lower_branch b hb hbπ

theorem rightInverseSlope_at_lower_branch (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    rightInverseSlope (1+Real.cos b) (-b) = 0 := by
  have hc : 0 < Real.cos (b/2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hcos : 1+Real.cos b = 2*(Real.cos (b/2))^2 := by
    have hh := Real.cos_two_mul (b/2)
    rw [show 2*(b/2)=b by ring] at hh
    nlinarith
  have hsin : Real.sin b = 2*Real.sin (b/2)*Real.cos (b/2) := by
    simpa only [show 2*(b/2)=b by ring] using Real.sin_two_mul (b/2)
  have hdisc : inverseDiscriminant (1+Real.cos b) (-b) = (Real.sin b)^2 := by
    unfold inverseDiscriminant
    rw [show -b/2 = -(b/2) by ring, Real.cos_neg]
    nlinarith [Real.sin_sq_add_cos_sq b]
  unfold rightInverseSlope
  rw [hdisc, Real.sqrt_sq hs.le, show -b/2 = -(b/2) by ring, Real.sin_neg,
    Real.cos_neg]
  have hc0 : Real.cos (b/2) ≠ 0 := ne_of_gt hc
  have hs0 : Real.sin b ≠ 0 := ne_of_gt hs
  field_simp
  nlinarith [hcos, hsin]

/-- The vanishing slope at the moving branch is verified from the formula. -/
theorem rightInverse_deriv_at_lower_branch (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    deriv (rightInverse (1+Real.cos b)) (-b) = 0 := by
  have hc : 0 < Real.cos (-b/2) := by
    rw [show -b/2 = -(b/2) by ring, Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hh := Real.cos_two_mul (b/2)
  rw [show 2*(b/2)=b by ring] at hh
  have hD : 0 < inverseDiscriminant (1+Real.cos b) (-b) := by
    unfold inverseDiscriminant
    rw [show -b/2 = -(b/2) by ring, Real.cos_neg]
    nlinarith [Real.sin_sq_add_cos_sq b]
  rw [rightInverse_deriv _ _ hc hD, rightInverseSlope_at_lower_branch b hb hbπ]

/-! An explicit complex realization of the same inverse.  The slit conditions
below are local branch-domain conditions, not assumptions of any tail or
transport conclusion. -/

def preferredCosineRoot (z : ℂ) : ℂ := z+Complex.I*Complex.sqrt (1-z^2)

theorem preferredCosineRoot_mul (z : ℂ) :
    preferredCosineRoot z*(z-Complex.I*Complex.sqrt (1-z^2)) = 1 := by
  have hs : (Complex.sqrt (1-z^2))^2 = 1-z^2 :=
    Complex.cpow_nat_inv_pow (1-z^2) (by norm_num : (2:ℕ) ≠ 0)
  calc
    _ = z^2-Complex.I^2*(Complex.sqrt (1-z^2))^2 := by
      unfold preferredCosineRoot
      ring
    _ = 1 := by rw [Complex.I_sq, hs]; ring

theorem preferredCosineRoot_ne_zero (z : ℂ) : preferredCosineRoot z ≠ 0 := by
  intro h
  have hp := preferredCosineRoot_mul z
  rw [h, zero_mul] at hp
  exact zero_ne_one hp

theorem preferredCosineRoot_trace (z : ℂ) :
    preferredCosineRoot z+(preferredCosineRoot z)⁻¹ = 2*z := by
  rw [inv_eq_of_mul_eq_one_right (preferredCosineRoot_mul z)]
  unfold preferredCosineRoot
  ring

def preferredArccos (z : ℂ) : ℂ := -Complex.I*Complex.log (preferredCosineRoot z)

theorem cos_preferredArccos (z : ℂ) : Complex.cos (preferredArccos z) = z := by
  have he : preferredArccos z * Complex.I = Complex.log (preferredCosineRoot z) := by
    unfold preferredArccos
    calc
      _ = -(Complex.I*Complex.I)*Complex.log (preferredCosineRoot z) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Complex.cos, he, neg_mul, he, Complex.exp_neg,
    Complex.exp_log (preferredCosineRoot_ne_zero z), preferredCosineRoot_trace]
  ring

def complexRightInverse (S v : ℂ) : ℂ :=
  v/2-preferredArccos (S/(2*Complex.cos (v/2)))

/-- Exact dispersion identity for (6.1) in the chosen complex realization. -/
theorem complexRightInverse_dispersion (S v : ℂ) (hc : Complex.cos (v/2) ≠ 0) :
    Complex.cos (complexRightInverse S v) +
      Complex.cos (v-complexRightInverse S v) = S := by
  unfold complexRightInverse
  rw [show v-(v/2-preferredArccos (S/(2*Complex.cos (v/2)))) =
      v/2+preferredArccos (S/(2*Complex.cos (v/2))) by ring,
    Complex.cos_sub, Complex.cos_add, cos_preferredArccos]
  field_simp
  ; ring

theorem complexRightInverse_analyticAt (S v : ℂ)
    (hc : Complex.cos (v/2) ≠ 0)
    (hsqrt : 1-(S/(2*Complex.cos (v/2)))^2 ∈ Complex.slitPlane)
    (hlog : preferredCosineRoot (S/(2*Complex.cos (v/2))) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => complexRightInverse z.1 z.2) (S,v) := by
  have hhalf : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2/2) (S,v) :=
    analyticAt_snd.div_const
  have hcos : AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.cos (z.2/2)) (S,v) :=
    Complex.analyticAt_cos.comp hhalf
  have hratio : AnalyticAt ℂ
      (fun z : ℂ × ℂ => z.1/(2*Complex.cos (z.2/2))) (S,v) :=
    analyticAt_fst.div (analyticAt_const.mul hcos) (by exact mul_ne_zero (by norm_num) hc)
  have harg : AnalyticAt ℂ
      (fun z : ℂ × ℂ => 1-(z.1/(2*Complex.cos (z.2/2)))^2) (S,v) :=
    analyticAt_const.sub (hratio.pow 2)
  have hs : AnalyticAt ℂ Complex.sqrt (1-(S/(2*Complex.cos (v/2)))^2) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hsqrt)
  have hroot : AnalyticAt ℂ
      (fun z : ℂ × ℂ => preferredCosineRoot (z.1/(2*Complex.cos (z.2/2)))) (S,v) :=
    hratio.add (analyticAt_const.mul (AnalyticAt.comp (f := fun z : ℂ × ℂ => 1-(z.1/(2*Complex.cos (z.2/2)))^2) (g := Complex.sqrt) hs harg))
  have harc : AnalyticAt ℂ
      (fun z : ℂ × ℂ => preferredArccos (z.1/(2*Complex.cos (z.2/2)))) (S,v) :=
    analyticAt_const.mul (hroot.clog hlog)
  exact hhalf.sub harc

/-- Every fixed mixed jet of the explicit inverse is uniformly bounded on
any compact branch-domain set. The compact domain is independent of the
particle count. -/
theorem complexRightInverse_compact_jets (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hc : ∀ z ∈ K, Complex.cos (z.2/2) ≠ 0)
    (hsqrt : ∀ z ∈ K, 1-(z.1/(2*Complex.cos (z.2/2)))^2 ∈ Complex.slitPlane)
    (hlog : ∀ z ∈ K, preferredCosineRoot (z.1/(2*Complex.cos (z.2/2))) ∈ Complex.slitPlane)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      ‖iteratedFDeriv ℂ j (fun p : ℂ × ℂ => complexRightInverse p.1 p.2) z‖ ≤ C := by
  have ha : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => complexRightInverse p.1 p.2) K := by
    intro z hz
    exact complexRightInverse_analyticAt z.1 z.2 (hc z hz) (hsqrt z hz) (hlog z hz)
  have hcont : ContinuousOn
      (iteratedFDeriv ℂ j (fun p : ℂ × ℂ => complexRightInverse p.1 p.2)) K := by
    intro z hz
    exact ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0+1, by positivity, ?_⟩
  intro z hz
  exact (hC z hz).trans (by have := le_max_left C 0; linarith)

theorem preferred_sqrt_ofReal (x : ℝ) (hx : 0 ≤ x) :
    Complex.sqrt (x:ℂ) = (Real.sqrt x:ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, add_self_div_two]

theorem preferredCosineRoot_re (a : ℝ) (ha : 0 ≤ 1-a^2) :
    (preferredCosineRoot (a:ℂ)).re = a := by
  unfold preferredCosineRoot
  rw [show (1-(a:ℂ)^2) = ((1-a^2:ℝ):ℂ) by push_cast; rfl,
    preferred_sqrt_ofReal _ ha]
  simp

/-- The branch-domain conditions are consequences of the actual real right-arc
inequalities, rather than additional physical input. -/
theorem complexRightInverse_analyticAt_real (S v : ℝ) (hS : 0 < S)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => complexRightInverse z.1 z.2)
      ((S:ℂ),(v:ℂ)) := by
  have hcomplex : Complex.cos ((v:ℂ)/2) = (Real.cos (v/2):ℂ) := by
    rw [show (v:ℂ)/2 = ((v/2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cos]
  have hratio : (S:ℂ)/(2*Complex.cos ((v:ℂ)/2)) =
      ((S/(2*Real.cos (v/2)):ℝ):ℂ) := by
    rw [hcomplex]
    push_cast
    rfl
  have hm := abs_lt.mp (inverseDiscriminant_arccos_margin hc hD)
  have hA : 0 < 1-(S/(2*Real.cos (v/2)))^2 := by nlinarith
  apply complexRightInverse_analyticAt
  · rw [hcomplex]
    exact_mod_cast (ne_of_gt hc)
  · rw [hratio]
    left
    simp only [Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    exact hA
  · rw [hratio]
    left
    rw [preferredCosineRoot_re _ hA.le]
    exact div_pos hS (by positivity)

theorem preferredCosineRoot_cos (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    preferredCosineRoot (Real.cos b:ℂ) = Complex.exp ((b:ℂ)*Complex.I) := by
  have hs : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hsq : (1-(Real.cos b:ℂ)^2) = ((Real.sin b)^2:ℂ) := by
    have h := Real.sin_sq_add_cos_sq b
    have he : 1-(Real.cos b)^2 = (Real.sin b)^2 := by linarith
    exact_mod_cast he
  rw [preferredCosineRoot, hsq,
    show ((Real.sin b)^2:ℂ) = (((Real.sin b)^2:ℝ):ℂ) by push_cast; rfl,
    preferred_sqrt_ofReal _ (sq_nonneg _), Real.sqrt_sq hs.le,
    Complex.exp_ofReal_mul_I]
  ring

theorem preferredArccos_cos (b : ℝ) (hb : 0 < b) (hbπ : b < Real.pi) :
    preferredArccos (Real.cos b:ℂ) = (b:ℂ) := by
  unfold preferredArccos
  rw [preferredCosineRoot_cos b hb hbπ, Complex.log_exp]
  · ring_nf
    simp [Complex.I_sq]
  · simpa using (show -Real.pi < b by linarith [Real.pi_pos])
  · simpa using hbπ.le

theorem preferredArccos_ofReal (a : ℝ) (ha : -1 < a) (ha' : a < 1) :
    preferredArccos (a:ℂ) = (Real.arccos a:ℂ) := by
  have hb : 0 < Real.arccos a := Real.arccos_pos.mpr ha'
  have hbπ : Real.arccos a < Real.pi := Real.arccos_lt_pi.mpr ha
  have hc := Real.cos_arccos ha.le ha'.le
  simpa only [hc] using preferredArccos_cos (Real.arccos a) hb hbπ

/-- The complex inverse is the declared real inverse on the right arc. -/
theorem complexRightInverse_ofReal (S v : ℝ)
    (hc : 0 < Real.cos (v/2)) (hD : 0 < inverseDiscriminant S v) :
    complexRightInverse (S:ℂ) (v:ℂ) = (rightInverse S v:ℂ) := by
  have hm := abs_lt.mp (inverseDiscriminant_arccos_margin hc hD)
  have hcos : Complex.cos ((v:ℂ)/2) = (Real.cos (v/2):ℂ) := by
    rw [show (v:ℂ)/2 = ((v/2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cos]
  unfold complexRightInverse rightInverse
  rw [hcos, show (S:ℂ)/(2*(Real.cos (v/2):ℂ)) =
      ((S/(2*Real.cos (v/2)):ℝ):ℂ) by push_cast; rfl,
    preferredArccos_ofReal _ hm.1 hm.2]
  push_cast
  rfl

/-! Exact transfer of the proper local branch estimates to the Preferred
outward plateau.  No full-tail theorem is imported by BranchCone. -/

structure PreferredBranchData where
  alpha : ℝ
  b : ℝ
  alpha_pos : 0 < alpha
  alpha_lt : alpha < Real.pi/2
  b_pos : 0 < b
  b_lt : b < Real.pi
  angle_relation : Real.cos b = 2*Real.cos alpha-1

def PreferredBranchData.localData (d : PreferredBranchData) : IsingBulk.Branch.LocalBranchData where
  theta := d.alpha
  thetaB := d.b
  c₀ := Real.sin d.alpha/Real.sin d.b
  tau := 2
  alpha := 1
  theta_pos := d.alpha_pos
  theta_lt := d.alpha_lt
  thetaB_pos := d.b_pos
  thetaB_lt := d.b_lt
  angle_relation := d.angle_relation
  c₀_pos := div_pos
    (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt, Real.pi_pos]))
    (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt)
  margin := by
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt))]
    have hs := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt, Real.pi_pos])
    linarith
  tau_pos := by norm_num
  alpha_pos := by norm_num

/-- The literal Preferred outward plateau, with δ the common outward shift. -/
def outwardPlateauW (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  IsingBulk.Branch.plateauW (IsingBulk.Branch.radialParameter d.alpha ε) δ d.b (u:ℂ)

def outwardPlateauPhase (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  preferredArccos (outwardPlateauW d ε δ u)

def outwardPlateauAngle (d : PreferredBranchData) (δ u : ℝ) : ℂ :=
  ((-d.b+u:ℝ):ℂ)-Complex.I*(δ:ℂ)

theorem outwardPlateauW_formula (d : PreferredBranchData) (ε δ u : ℝ) :
    outwardPlateauW d ε δ u =
      IsingBulk.Branch.radialParameter d.alpha ε+
        (IsingBulk.Branch.radialParameter d.alpha ε)⁻¹-
        Complex.cos (outwardPlateauAngle d δ u) := by
  unfold outwardPlateauW IsingBulk.Branch.plateauW outwardPlateauAngle
  have he : (δ:ℂ)+(-(d.b:ℂ)+(u:ℂ))*Complex.I =
      (((-d.b+u:ℝ):ℂ)-Complex.I*(δ:ℂ))*Complex.I := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he, Complex.cosh_mul_I]

theorem outwardPlateauPhase_cos (d : PreferredBranchData) (ε δ u : ℝ) :
    Complex.cos (outwardPlateauPhase d ε δ u) = outwardPlateauW d ε δ u :=
  cos_preferredArccos _

theorem outwardPlateauW_transfer (d : PreferredBranchData) (ε δ u : ℝ) :
    IsingBulk.Branch.currentW d.localData ε (δ+d.localData.c₀*ε) u =
      outwardPlateauW d ε δ u := by
  unfold IsingBulk.Branch.currentW outwardPlateauW
  change IsingBulk.Branch.plateauW _
    (-d.localData.c₀*ε+2*(δ+d.localData.c₀*ε)/2) _ _ = _
  rw [show -d.localData.c₀*ε+2*(δ+d.localData.c₀*ε)/2 = δ by ring]
  rfl

theorem outwardPlateauPhase_transfer (d : PreferredBranchData) (ε δ u : ℝ) :
    IsingBulk.Branch.currentPhase d.localData ε (δ+d.localData.c₀*ε) u =
      outwardPlateauPhase d ε δ u := by
  unfold IsingBulk.Branch.currentPhase outwardPlateauPhase
  rw [outwardPlateauW_transfer]
  rfl

def outwardTransferRadius (d : PreferredBranchData) (r : ℝ) : ℝ :=
  r/(2*(1+d.localData.c₀))

theorem outwardTransferRadius_pos (d : PreferredBranchData) {r : ℝ} (hr : 0 < r) :
    0 < outwardTransferRadius d r := by
  unfold outwardTransferRadius
  have hc := d.localData.c₀_pos
  positivity

theorem outwardTransfer_small (d : PreferredBranchData) {r ε δ u : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hεr : ε < outwardTransferRadius d r)
    (hδ : 0 ≤ δ) (hδr : δ < outwardTransferRadius d r)
    (hur : |u| < outwardTransferRadius d r) :
    ε < r ∧ 0 ≤ δ+d.localData.c₀*ε ∧ δ+d.localData.c₀*ε < r ∧ |u| < r := by
  have hc := d.localData.c₀_pos
  have hscale : (1+d.localData.c₀)*outwardTransferRadius d r = r/2 := by
    unfold outwardTransferRadius
    field_simp
  have hrho := outwardTransferRadius_pos d hr
  have hrhor : outwardTransferRadius d r < r := by nlinarith
  refine ⟨hεr.trans hrhor, by positivity, ?_, hur.trans hrhor⟩
  nlinarith [mul_lt_mul_of_pos_left hεr hc]

/-- A square root in the source 7/10 cone obeys the 6/5 component cone
needed for the oblique reciprocal-cube estimate. -/
theorem preferred_sqrt_component_cone (z : ℂ) (hzr : 0 < z.re) (hzi : z.im < 0)
    (hcone : (7/10:ℝ)*‖z‖ ≤ z.re) :
    0 ≤ -z.im ∧ -z.im ≤ (6/5:ℝ)*z.re := by
  have hn := norm_nonneg z
  have hs : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hc := mul_self_le_mul_self (by positivity : 0 ≤ (7/10:ℝ)*‖z‖) hcone
  refine ⟨by linarith, ?_⟩
  by_contra h
  have hgt : (6/5:ℝ)*z.re < -z.im := lt_of_not_ge h
  have hsq := mul_self_lt_mul_self (by positivity : 0 ≤ (6/5:ℝ)*z.re) hgt
  nlinarith

/-- Uniform physical sine size and fourth-quadrant cone on the exact
Preferred outward lower-branch plateau, including u=0 and δ=0. -/
theorem preferred_outward_branch_control (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ u → u < r →
      c*Real.sqrt (u+ε+δ) ≤ ‖Complex.sin (outwardPlateauPhase d ε δ u)‖ ∧
      ‖Complex.sin (outwardPlateauPhase d ε δ u)‖ ≤ C*Real.sqrt (u+ε+δ) ∧
      0 < (Complex.sin (outwardPlateauPhase d ε δ u)).re ∧
      0 ≤ -(Complex.sin (outwardPlateauPhase d ε δ u)).im ∧
      -(Complex.sin (outwardPlateauPhase d ε δ u)).im ≤
        (6/5:ℝ)*(Complex.sin (outwardPlateauPhase d ε δ u)).re ∧
      0 < (outwardPlateauPhase d ε δ u).re ∧
      (outwardPlateauPhase d ε δ u).re < Real.pi/2 ∧
      (outwardPlateauPhase d ε δ u).im < 0 := by
  let e := d.localData
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmod⟩ := IsingBulk.Branch.current_modulus_Q e
  obtain ⟨r₂,hr₂,hmargin⟩ :=
    IsingBulk.Branch.current_positive_factor_margin e (1/50) (by norm_num)
  obtain ⟨r₃,hr₃,hbranch⟩ := IsingBulk.Branch.current_branch_inclusion e
  obtain ⟨r₄,hr₄,hfactor⟩ := Metric.eventually_nhds_iff.mp
    (IsingBulk.Branch.current_factors_near_zero e)
  let r₀ := min r₁ (min r₂ (min r₃ r₄))
  have hr₀ : 0 < r₀ := lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hr₄))
  let K := 2+2*e.c₀
  have hK : 0 < K := by dsimp [K]; have := e.c₀_pos; positivity
  refine ⟨Real.sqrt c, Real.sqrt (3*C*K), outwardTransferRadius d r₀,
    Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr (by positivity),
    outwardTransferRadius_pos d hr₀, ?_⟩
  intro ε δ u hε hεr hδ hδr hu hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr₀ hε hεr hδ hδr
    (by simpa only [abs_of_nonneg hu] using hur)
  have h1 : r₀ ≤ r₁ := min_le_left _ _
  have h2 : r₀ ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r₀ ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : r₀ ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let t := δ+e.c₀*ε
  have htime : 0 ≤ t := ht
  obtain ⟨hlo,hhi⟩ := hmod ε t u hε (he.trans_le h1) htime (ht'.trans_le h1) (hu'.trans_le h1)
  have hm := hmargin ε t u hε (he.trans_le h2) htime (ht'.trans_le h2) hu
    (by simpa only [abs_of_nonneg hu] using hu'.trans_le h2)
  obtain ⟨hwr,hwi⟩ := hbranch ε t u hε (he.trans_le h3) htime (ht'.trans_le h3) (hu'.trans_le h3)
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₄ := by
    simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε,
      abs_of_nonneg htime, abs_of_nonneg hu, max_lt_iff] using
      And.intro (he.trans_le h4) (And.intro (ht'.trans_le h4)
        (by simpa only [abs_of_nonneg hu] using hu'.trans_le h4))
  obtain ⟨_,_,hflo,hfhi⟩ := hfactor hz
  let W := IsingBulk.Branch.currentW e ε t u
  let D := IsingBulk.Branch.currentD e ε t u
  let z := Complex.sqrt (1-W^2)
  have hfactorization : 1-W^2 = D*(2-D) := by dsimp [W,D,IsingBulk.Branch.currentD]; ring
  have hnsq : ‖z‖^2 = ‖D‖*‖2-D‖ := by
    rw [← norm_pow, IsingBulk.Branch.sqrt_sq, hfactorization, norm_mul]
  have hnormlo : c*(u+ε+δ) ≤ ‖z‖^2 := by
    have hQ : u+ε+δ ≤ |u|+ε+e.tau*t := by
      dsimp [t,e,PreferredBranchData.localData]
      rw [abs_of_nonneg hu]
      have hs := d.localData.c₀_pos
      change 0 < Real.sin d.alpha/Real.sin d.b at hs
      nlinarith
    have hcQ := mul_le_mul_of_nonneg_left hQ hc.le
    rw [hnsq]
    change 1 ≤ ‖2-D‖ at hflo
    change c*(|u|+ε+e.tau*t) ≤ ‖D‖ at hlo
    nlinarith [mul_le_mul_of_nonneg_left hflo (norm_nonneg D)]
  have hnormhi : ‖z‖^2 ≤ 3*C*K*(u+ε+δ) := by
    have hQ : |u|+ε+e.tau*t ≤ K*(u+ε+δ) := by
      dsimp [K,t]
      change |u|+ε+2*(δ+e.c₀*ε) ≤ (2+2*e.c₀)*(u+ε+δ)
      rw [abs_of_nonneg hu]
      nlinarith [mul_nonneg e.c₀_pos.le hu, mul_nonneg e.c₀_pos.le hδ]
    have hcQ := mul_le_mul_of_nonneg_left hQ hC.le
    rw [hnsq]
    change ‖2-D‖ ≤ 3 at hfhi
    change ‖D‖ ≤ C*(|u|+ε+e.tau*t) at hhi
    nlinarith [mul_le_mul_of_nonneg_left hfhi (norm_nonneg D)]
  have hzim : (1-W^2).im < 0 := by
    simp only [pow_two, Complex.sub_im, Complex.one_im, Complex.mul_im]
    change 0 < W.re at hwr
    change 0 < W.im at hwi
    nlinarith [mul_pos hwr hwi]
  obtain ⟨hzr,hzi⟩ := IsingBulk.Branch.sqrt_lower_orientation (1-W^2) hzim
  have hcone := IsingBulk.Branch.sqrt_cone_of_real_margin (1-W^2) hzim hm
  have hcomponents := preferred_sqrt_component_cone z hzr hzi hcone
  have hsine : Complex.sin (outwardPlateauPhase d ε δ u) = z := by
    rw [← outwardPlateauPhase_transfer]
    exact IsingBulk.Branch.sin_lowerArccos W
  have hsheet := IsingBulk.Branch.lowerArccos_sheet W hwr hwi
  have hphase : outwardPlateauPhase d ε δ u = IsingBulk.Branch.lowerArccos W := by
    rw [← outwardPlateauPhase_transfer]
    rfl
  rw [hsine, hphase]
  refine ⟨?_,?_,hzr,hcomponents.1,hcomponents.2,hsheet.2.1,hsheet.2.2.1,hsheet.2.2.2⟩
  · have hh := Real.sqrt_le_sqrt hnormlo
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg z)] at hh
    exact hh
  · have hh := Real.sqrt_le_sqrt hnormhi
    rw [Real.sqrt_mul (by positivity : 0 ≤ 3*C*K), Real.sqrt_sq (norm_nonneg z)] at hh
    exact hh

/-- The negative branch has the required square-root attenuation for the
Preferred outward shift, with no lower bound imposed on δ/ε. -/
theorem preferred_outward_negative_attenuation (d : PreferredBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → u ≤ 0 → |u| < r →
      c*Real.sqrt (|u|+ε+δ) ≤ -(outwardPlateauPhase d ε δ u).im := by
  obtain ⟨c,r,hc,hr,hbound⟩ := IsingBulk.Branch.current_negative_attenuation_Q d.localData
  refine ⟨c,outwardTransferRadius d r,hc,outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hu hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr hur
  have hb := hbound ε (δ+d.localData.c₀*ε) u hε he ht ht' hu hu'
  rw [outwardPlateauPhase_transfer] at hb
  have hQ : |u|+ε+δ ≤ |u|+ε+d.localData.tau*(δ+d.localData.c₀*ε) := by
    change |u|+ε+δ ≤ |u|+ε+2*(δ+d.localData.c₀*ε)
    have hc₀ := d.localData.c₀_pos
    nlinarith
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ) hc.le).trans hb

/-- The actual fixed-ε, fixed-δ angular derivative has its complete two-sided
square-root scale on both sides of the branch. -/
theorem preferred_outward_phase_derivative_size (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      c/Real.sqrt (|u|+ε+δ) ≤ ‖deriv (outwardPlateauPhase d ε δ) u‖ ∧
      ‖deriv (outwardPlateauPhase d ε δ) u‖ ≤ C/Real.sqrt (|u|+ε+δ) := by
  obtain ⟨c,C,r,hc,hC,hr,hbound⟩ := IsingBulk.Branch.current_derivative_magnitude_Q d.localData
  let K := 2+2*d.localData.c₀
  have hK : 0 < K := by dsimp [K]; have := d.localData.c₀_pos; positivity
  refine ⟨c/Real.sqrt K,C,outwardTransferRadius d r,by positivity,hC,
    outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr hur
  obtain ⟨hlo,hhi⟩ := hbound ε (δ+d.localData.c₀*ε) u hε he ht ht' hu'
  have hfun : IsingBulk.Branch.currentPhase d.localData ε (δ+d.localData.c₀*ε) =
      outwardPlateauPhase d ε δ := funext (outwardPlateauPhase_transfer d ε δ)
  rw [hfun] at hlo hhi
  let L := |u|+ε+δ
  let Q := |u|+ε+d.localData.tau*(δ+d.localData.c₀*ε)
  have hL : 0 < L := by dsimp [L]; positivity
  have hQL : L ≤ Q := by
    dsimp [L,Q]
    change |u|+ε+δ ≤ |u|+ε+2*(δ+d.localData.c₀*ε)
    nlinarith [d.localData.c₀_pos]
  have hQK : Q ≤ K*L := by
    dsimp [Q,K,L]
    change |u|+ε+2*(δ+d.localData.c₀*ε) ≤ (2+2*d.localData.c₀)*(|u|+ε+δ)
    nlinarith [abs_nonneg u, mul_nonneg d.localData.c₀_pos.le (abs_nonneg u),
      mul_nonneg d.localData.c₀_pos.le hδ]
  have hQpos : 0 < Q := hL.trans_le hQL
  have hslo := Real.sqrt_le_sqrt hQL
  have hshi := Real.sqrt_le_sqrt hQK
  rw [Real.sqrt_mul hK.le] at hshi
  constructor
  · apply le_trans _ hlo
    change (c/Real.sqrt K)/Real.sqrt L ≤ c/Real.sqrt Q
    rw [div_div]
    exact div_le_div₀ hc.le le_rfl (Real.sqrt_pos.mpr hQpos) hshi
  · exact hhi.trans (div_le_div₀ hC.le le_rfl (Real.sqrt_pos.mpr hL) hslo)


/-- The actual positive-side angular derivative stays in the source 2/3 cone. -/
theorem preferred_outward_phase_positive_cone (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ u → u < r →
      (2/3:ℝ)*‖deriv (outwardPlateauPhase d ε δ) u‖ ≤
        (deriv (outwardPlateauPhase d ε δ) u).re := by
  obtain ⟨r,hr,hbound⟩ := IsingBulk.Branch.current_positive_cone d.localData
  refine ⟨outwardTransferRadius d r,outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hu hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr
    (by simpa only [abs_of_nonneg hu] using hur)
  have hb := hbound ε (δ+d.localData.c₀*ε) u hε he ht ht' hu
    (by simpa only [abs_of_nonneg hu] using hu')
  have hfun : IsingBulk.Branch.currentPhase d.localData ε (δ+d.localData.c₀*ε) =
      outwardPlateauPhase d ε δ := funext (outwardPlateauPhase_transfer d ε δ)
  rwa [hfun] at hb

/-- At a common outward shift, the smallest nonnegative coordinate controls
all other positive-side first derivatives, uniformly through the branch. -/
theorem preferred_outward_minimum_derivative (d : PreferredBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε δ u v : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → 0 ≤ u → u ≤ v → v < r →
      ‖deriv (outwardPlateauPhase d ε δ) v‖ ≤
        C*‖deriv (outwardPlateauPhase d ε δ) u‖ := by
  obtain ⟨c,C,r,hc,hC,hr,hbound⟩ := preferred_outward_phase_derivative_size d
  refine ⟨C/c,r,div_pos hC hc,hr,?_⟩
  intro ε δ u v hε hεr hδ hδr hu huv hvr
  have hv := hu.trans huv
  have hur : |u| < r := by rw [abs_of_nonneg hu]; exact huv.trans_lt hvr
  have hvr' : |v| < r := by rwa [abs_of_nonneg hv]
  have hlo := (hbound ε δ u hε hεr hδ hδr hur).1
  have hhi := (hbound ε δ v hε hεr hδ hδr hvr').2
  rw [abs_of_nonneg hu] at hlo
  rw [abs_of_nonneg hv] at hhi
  have hpos : 0 < u+ε+δ := by positivity
  have hscale := Real.sqrt_le_sqrt (show u+ε+δ ≤ v+ε+δ by linarith)
  have hcmp := div_le_div₀ hC.le le_rfl (Real.sqrt_pos.mpr hpos) hscale
  have hm := mul_le_mul_of_nonneg_left hlo (le_of_lt (div_pos hC hc))
  calc
    _ ≤ C/Real.sqrt (v+ε+δ) := hhi
    _ ≤ C/Real.sqrt (u+ε+δ) := hcmp
    _ = (C/c)*(c/Real.sqrt (u+ε+δ)) := by field_simp
    _ ≤ (C/c)*‖deriv (outwardPlateauPhase d ε δ) u‖ := hm

def outwardPlateauD (d : PreferredBranchData) (ε δ u : ℝ) : ℂ :=
  1-outwardPlateauW d ε δ u

def outwardPlateauBeta (d : PreferredBranchData) (ε δ u : ℝ) : ℝ :=
  (outwardPlateauW d ε δ u).im

def outwardPlateauRealRemainder (d : PreferredBranchData) (ε δ u : ℝ) : ℝ :=
  (outwardPlateauD d ε δ u).re-Real.sin d.b*u

theorem outwardPlateauD_transfer (d : PreferredBranchData) (ε δ u : ℝ) :
    IsingBulk.Branch.currentD d.localData ε (δ+d.localData.c₀*ε) u =
      outwardPlateauD d ε δ u := by
  unfold IsingBulk.Branch.currentD outwardPlateauD
  rw [outwardPlateauW_transfer]

/-- Exact real and imaginary parts on the Preferred outward plateau. -/
theorem outwardPlateau_components (d : PreferredBranchData) (ε δ u : ℝ)
    (hε : 1+ε ≠ 0) :
    (outwardPlateauD d ε δ u).re =
      1-(2+ε^2/(1+ε))*Real.cos d.alpha+Real.cosh δ*Real.cos (d.b-u) ∧
    outwardPlateauBeta d ε δ u =
      (2*ε-ε^2/(1+ε))*Real.sin d.alpha+Real.sinh δ*Real.sin (d.b-u) := by
  have h := IsingBulk.Branch.current_components d.localData ε (δ+d.localData.c₀*ε) u hε
  rw [outwardPlateauD_transfer] at h
  have ht : -d.localData.c₀*ε+d.localData.tau*(δ+d.localData.c₀*ε)/2 = δ := by
    change -d.localData.c₀*ε+2*(δ+d.localData.c₀*ε)/2 = δ
    ring
  rw [ht] at h
  change (outwardPlateauD d ε δ u).re = _ ∧ -(outwardPlateauD d ε δ u).im = _ at h
  have hn : -d.localData.thetaB+u = -(d.b-u) := by change -d.b+u = _; ring
  rw [hn,Real.cos_neg,Real.sin_neg] at h
  constructor
  · exact h.1
  · simpa [outwardPlateauBeta,outwardPlateauD,PreferredBranchData.localData] using h.2

theorem outwardPlateau_normal_form_identity (d : PreferredBranchData) (ε δ u : ℝ) :
    outwardPlateauD d ε δ u =
      (Real.sin d.b:ℂ)*(u:ℂ)-Complex.I*(outwardPlateauBeta d ε δ u:ℂ)+
        (outwardPlateauRealRemainder d ε δ u:ℂ) := by
  apply Complex.ext <;>
    simp [outwardPlateauD,outwardPlateauBeta,outwardPlateauRealRemainder,Complex.mul_re,
      Complex.mul_im]

/-- Quantitative imaginary displacement on the literal outward plateau. -/
theorem preferred_outward_imaginary_margin (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      c*(ε+δ) ≤ outwardPlateauBeta d ε δ u ∧
        outwardPlateauBeta d ε δ u ≤ C*(ε+δ) := by
  obtain ⟨c,C,r,hc,hC,hr,hbound⟩ := IsingBulk.Branch.current_imaginary_margin d.localData
  let K := 2+2*d.localData.c₀
  have hK : 0 < K := by dsimp [K]; have := d.localData.c₀_pos; positivity
  refine ⟨c,C*K,outwardTransferRadius d r,hc,mul_pos hC hK,
    outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr hur
  obtain ⟨hlo,hhi⟩ := hbound ε (δ+d.localData.c₀*ε) u hε he ht ht' hu'
  rw [outwardPlateauW_transfer] at hlo hhi
  have hQlo : ε+δ ≤ ε+d.localData.tau*(δ+d.localData.c₀*ε) := by
    change ε+δ ≤ ε+2*(δ+d.localData.c₀*ε)
    nlinarith [d.localData.c₀_pos]
  have hQhi : ε+d.localData.tau*(δ+d.localData.c₀*ε) ≤ K*(ε+δ) := by
    change ε+2*(δ+d.localData.c₀*ε) ≤ (2+2*d.localData.c₀)*(ε+δ)
    nlinarith [mul_nonneg d.localData.c₀_pos.le hδ]
  refine ⟨(mul_le_mul_of_nonneg_left hQlo hc.le).trans hlo,?_⟩
  exact hhi.trans (by nlinarith [mul_le_mul_of_nonneg_left hQhi hC.le])

/-- The remainder in the source branch normal form is genuinely real and
quadratic in the actual displacement scale ε+δ. -/
theorem preferred_outward_real_remainder (d : PreferredBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      |outwardPlateauRealRemainder d ε δ u| ≤ C*(u^2+(ε+δ)^2) := by
  obtain ⟨C,r,hC,hr,hbound⟩ := IsingBulk.Branch.current_real_remainder d.localData
  let K := 2+2*d.localData.c₀
  have hK : 1 ≤ K := by dsimp [K]; have := d.localData.c₀_pos; linarith
  refine ⟨C*K^2,outwardTransferRadius d r,by positivity,
    outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr hur
  have hb := hbound ε (δ+d.localData.c₀*ε) u hε.le he ht ht' hu'
  rw [outwardPlateauD_transfer] at hb
  change |outwardPlateauRealRemainder d ε δ u| ≤
    C*(u^2+(ε+d.localData.tau*(δ+d.localData.c₀*ε))^2) at hb
  have hQ : ε+d.localData.tau*(δ+d.localData.c₀*ε) ≤ K*(ε+δ) := by
    change ε+2*(δ+d.localData.c₀*ε) ≤ (2+2*d.localData.c₀)*(ε+δ)
    nlinarith [mul_nonneg d.localData.c₀_pos.le hδ]
  have hQpos : 0 ≤ ε+d.localData.tau*(δ+d.localData.c₀*ε) := by
    have := d.localData.c₀_pos
    have := d.localData.tau_pos
    positivity
  have hsq := pow_le_pow_left₀ hQpos hQ 2
  have hu : u^2 ≤ K^2*u^2 := by nlinarith [sq_nonneg (K-1),sq_nonneg u]
  apply hb.trans
  nlinarith [mul_le_mul_of_nonneg_left hu hC.le,
    mul_le_mul_of_nonneg_left hsq hC.le]


/-- The phase exponential is the reciprocal of the explicit cosine root. -/
theorem preferred_exp_phase_inverse (W : ℂ) :
    Complex.exp (-Complex.I*preferredArccos W) = (preferredCosineRoot W)⁻¹ := by
  have he : -Complex.I*preferredArccos W = -Complex.log (preferredCosineRoot W) := by
    unfold preferredArccos
    ring_nf
    simp [Complex.I_sq]
  rw [he,Complex.exp_neg,Complex.exp_log (preferredCosineRoot_ne_zero W)]

/-- The explicit fourth-quadrant phase gives exactly the physical root
selected by its location inside the unit disk. -/
theorem preferred_phase_physical_root (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im) :
    Complex.exp (-Complex.I*preferredArccos W) = physicalRoot W := by
  rw [preferred_exp_phase_inverse]
  apply root_unique_in_disk (W := W)
  · simpa only [inv_inv,add_comm] using preferredCosineRoot_trace W
  · exact physicalRoot_trace W
  · exact inv_ne_zero (preferredCosineRoot_ne_zero W)
  · exact physicalRoot_ne_zero W
  · rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ (IsingBulk.Branch.inverseCosineRoot_norm W hre him)
  · exact physicalRoot_inside (Or.inl him.ne')

/-- The exact outward plateau lies uniformly in the first-quadrant W-domain
of the physical logarithmic chart on both sides of the branch. -/
theorem preferred_outward_branch_domain (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      0 < (outwardPlateauW d ε δ u).re ∧ 0 < (outwardPlateauW d ε δ u).im := by
  obtain ⟨r,hr,hbound⟩ := IsingBulk.Branch.current_branch_inclusion d.localData
  refine ⟨outwardTransferRadius d r,outwardTransferRadius_pos d hr,?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr hε hεr hδ hδr hur
  simpa only [outwardPlateauW_transfer] using hbound ε (δ+d.localData.c₀*ε) u hε he ht ht' hu'

theorem preferred_outward_physical_root (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      Complex.exp (-Complex.I*outwardPlateauPhase d ε δ u) =
        physicalRoot (outwardPlateauW d ε δ u) := by
  obtain ⟨r,hr,hbound⟩ := preferred_outward_branch_domain d
  refine ⟨r,hr,?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨hre,him⟩ := hbound ε δ u hε hεr hδ hδr hur
  exact preferred_phase_physical_root _ hre him

/-- The angular derivative of the exact outward phase, with occupancies and
hence δ held fixed, is the derivative from the physical dispersion relation. -/
theorem outwardPlateauPhase_hasDerivAt (d : PreferredBranchData) (ε δ u : ℝ)
    (hre : 0 < (outwardPlateauW d ε δ u).re)
    (him : 0 < (outwardPlateauW d ε δ u).im) :
    HasDerivAt (outwardPlateauPhase d ε δ)
      (-Complex.sin (outwardPlateauAngle d δ u)/
        Complex.sin (outwardPlateauPhase d ε δ u)) u := by
  have hfun : IsingBulk.Branch.currentPhase d.localData ε (δ+d.localData.c₀*ε) =
      outwardPlateauPhase d ε δ := funext (outwardPlateauPhase_transfer d ε δ)
  have ht : -d.localData.c₀*ε+d.localData.tau*(δ+d.localData.c₀*ε)/2 = δ := by
    change -d.localData.c₀*ε+2*(δ+d.localData.c₀*ε)/2 = δ
    ring
  have hdu : IsingBulk.Branch.currentDu d.localData ε (δ+d.localData.c₀*ε) u =
      -Complex.sin (outwardPlateauAngle d δ u) := by
    unfold IsingBulk.Branch.currentDu
    rw [ht]
    have he : (δ:ℂ)+(-(d.localData.thetaB:ℂ)+(u:ℂ))*Complex.I =
        outwardPlateauAngle d δ u*Complex.I := by
      unfold outwardPlateauAngle
      change (δ:ℂ)+(-(d.b:ℂ)+(u:ℂ))*Complex.I = _
      push_cast
      ring_nf
      simp [Complex.I_sq]
    rw [he,Complex.sinh_mul_I,mul_assoc,Complex.I_mul_I]
    ring
  have hd := IsingBulk.Branch.currentPhase_hasDerivAt d.localData ε (δ+d.localData.c₀*ε) u
    (by rwa [outwardPlateauW_transfer]) (by rwa [outwardPlateauW_transfer])
  rwa [hfun,hdu] at hd

/-- Exact derivative of the source imaginary displacement. -/
theorem outwardPlateauBeta_hasDerivAt (d : PreferredBranchData) (ε δ u : ℝ)
    (hε : 1+ε ≠ 0) :
    HasDerivAt (outwardPlateauBeta d ε δ)
      (-Real.sinh δ*Real.cos (d.b-u)) u := by
  have he : outwardPlateauBeta d ε δ = fun v =>
      (2*ε-ε^2/(1+ε))*Real.sin d.alpha+Real.sinh δ*Real.sin (d.b-v) :=
    funext (fun v => (outwardPlateau_components d ε δ v hε).2)
  rw [he]
  have hd := (((Real.hasDerivAt_sin (d.b-u)).comp u
    ((hasDerivAt_id u).const_sub d.b)).const_mul (Real.sinh δ)).const_add
      ((2*ε-ε^2/(1+ε))*Real.sin d.alpha)
  convert! hd using 1
  ring

/-- The u-dependence of β has precisely an outward-displacement cost. -/
theorem preferred_outward_beta_derivative_bound (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → 0 ≤ δ → δ < r →
      |deriv (outwardPlateauBeta d ε δ) u| ≤ 2*(ε+δ) := by
  have he : ∀ᶠ v in 𝓝 (0:ℝ), |IsingBulk.Branch.sinhQuotient v| < 2 :=
    IsingBulk.Branch.sinhQuotient_continuous.abs.eventually_lt continuousAt_const
      (by rw [IsingBulk.Branch.sinhQuotient_zero]; norm_num)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro ε δ u hε hδ hδr
  have hs := (hball (y := δ)
    (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hδ] using hδr)).le
  have hsinh : |Real.sinh δ| ≤ 2*δ := by
    rw [← IsingBulk.Branch.sinhQuotient_identity,abs_mul,abs_of_nonneg hδ]
    nlinarith [mul_le_mul_of_nonneg_left hs hδ]
  rw [(outwardPlateauBeta_hasDerivAt d ε δ u (by linarith)).deriv,abs_mul,abs_neg]
  have hh := mul_le_mul hsinh (Real.abs_cos_le_one (d.b-u)) (abs_nonneg _) (by positivity : 0 ≤ 2*δ)
  nlinarith


/-- The logarithmic arccos chart is analytic at every interior real point,
including negative W, which occurs on the compact right arc. -/
theorem preferredArccos_analyticAt_real (a : ℝ) (ha : -1 < a) (ha' : a < 1) :
    AnalyticAt ℂ preferredArccos (a:ℂ) := by
  have hA : 0 < 1-a^2 := by nlinarith
  have hcast : 1-(a:ℂ)^2 = ((1-a^2:ℝ):ℂ) := by push_cast; rfl
  have hs : AnalyticAt ℂ Complex.sqrt (1-(a:ℂ)^2) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (Or.inl (by rw [hcast]; exact hA)))
  have harg : AnalyticAt ℂ (fun z : ℂ => 1-z^2) (a:ℂ) := by fun_prop
  have hroot : AnalyticAt ℂ preferredCosineRoot (a:ℂ) :=
    analyticAt_id.add (analyticAt_const.mul
      (AnalyticAt.comp (f := fun z : ℂ => 1-z^2) (g := Complex.sqrt) hs harg))
  have him : 0 < (preferredCosineRoot (a:ℂ)).im := by
    unfold preferredCosineRoot
    rw [hcast,preferred_sqrt_ofReal _ hA.le]
    simpa using Real.sqrt_pos.mpr hA
  exact analyticAt_const.mul (hroot.clog (Or.inr him.ne'))

/-- The source trace is strictly between 0 and 2 at the selected root. -/
theorem preferred_reference_trace_range (d : PreferredBranchData) :
    0 < 1+Real.cos d.b ∧ 1+Real.cos d.b < 2 := by
  have hcospos : 0 < Real.cos d.alpha :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ) ≤ 0 by rfl)
    (show d.alpha ≤ Real.pi by linarith [d.alpha_lt,Real.pi_pos]) d.alpha_pos
  rw [Real.cos_zero] at hcoslt
  rw [d.angle_relation]
  constructor <;> linarith

/-- Every compact subinterval of the actual real right arc stays strictly
inside the arccos interval; the upper endpoint may be positive. -/
theorem preferred_right_reference_margin (d : PreferredBranchData)
    {ρ δR θ : ℝ} (hρ : 0 < ρ) (hδR : δR < d.b)
    (hθ : θ ∈ Set.Icc (-d.b+ρ) δR) :
    -1 < 1+Real.cos d.b-Real.cos θ ∧
      1+Real.cos d.b-Real.cos θ < 1 := by
  have habs : |θ| < d.b := abs_lt.mpr ⟨by linarith [hθ.1],hθ.2.trans_lt hδR⟩
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) d.b_lt.le habs
  rw [Real.cos_abs] at hcos
  obtain ⟨hS,_⟩ := preferred_reference_trace_range d
  constructor
  · linarith [Real.cos_le_one θ]
  · linarith

def preferredPhaseCurvature (S w : ℂ) : ℂ :=
  S*(1-S*Complex.cos w+(Complex.cos w)^2)/
    (Complex.sin (preferredArccos (S-Complex.cos w)))^3

/-- Positive reference curvature is derived from the literal dispersion
quotient, rather than supplied as a regularity hypothesis. -/
theorem preferred_reference_curvature_lower {S θ : ℝ}
    (hS : 0 < S) (hS' : S < 2)
    (hW : -1 < S-Real.cos θ) (hW' : S-Real.cos θ < 1) :
    0 < S*(1-S^2/4) ∧
    preferredPhaseCurvature (S:ℂ) (θ:ℂ) =
      ((S*(1-S*Real.cos θ+(Real.cos θ)^2)/
        (Real.sin (Real.arccos (S-Real.cos θ)))^3:ℝ):ℂ) ∧
    S*(1-S^2/4) ≤ (preferredPhaseCurvature (S:ℂ) (θ:ℂ)).re := by
  have hA : 0 < S*(1-S^2/4) := by
    have : 0 < 1-S^2/4 := by nlinarith
    positivity
  have hs : 0 < Real.sin (Real.arccos (S-Real.cos θ)) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW') (Real.arccos_lt_pi.mpr hW)
  have hN : S*(1-S^2/4) ≤ S*(1-S*Real.cos θ+(Real.cos θ)^2) := by
    nlinarith [mul_nonneg hS.le (sq_nonneg (Real.cos θ-S/2))]
  have hden : (Real.sin (Real.arccos (S-Real.cos θ)))^3 ≤ 1 :=
    pow_le_one₀ hs.le (Real.sin_le_one _)
  have he : preferredPhaseCurvature (S:ℂ) (θ:ℂ) =
      ((S*(1-S*Real.cos θ+(Real.cos θ)^2)/
        (Real.sin (Real.arccos (S-Real.cos θ)))^3:ℝ):ℂ) := by
    unfold preferredPhaseCurvature
    rw [← Complex.ofReal_cos,
      show (S:ℂ)-(Real.cos θ:ℂ) = ((S-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
      preferredArccos_ofReal _ hW hW',← Complex.ofReal_sin]
    push_cast
    rfl
  refine ⟨hA,he,?_⟩
  rw [he,Complex.ofReal_re]
  apply (le_div_iff₀ (pow_pos hs 3)).mpr
  exact (mul_le_mul_of_nonneg_left hden hA.le).trans (by simpa using hN)

/-- Joint continuity of the actual positive curvature quotient near any
point of the real reference right arc. -/
theorem preferredPhaseCurvature_continuousAt_real {S θ : ℝ}
    (hW : -1 < S-Real.cos θ) (hW' : S-Real.cos θ < 1) :
    ContinuousAt (fun z : ℂ × ℂ => preferredPhaseCurvature z.1 z.2)
      ((S:ℂ),(θ:ℂ)) := by
  have harg : ContinuousAt (fun z : ℂ × ℂ => z.1-Complex.cos z.2)
      ((S:ℂ),(θ:ℂ)) := by fun_prop
  have harc : ContinuousAt (fun z : ℂ × ℂ => preferredArccos (z.1-Complex.cos z.2))
      ((S:ℂ),(θ:ℂ)) :=
    ((preferredArccos_analyticAt_real _ hW hW').continuousAt).comp_of_eq harg
      (by rw [← Complex.ofReal_cos]; push_cast; rfl)
  have hsine := Complex.continuous_sin.continuousAt.comp harc
  have hsn : Complex.sin (preferredArccos ((S:ℂ)-Complex.cos (θ:ℂ))) ≠ 0 := by
    rw [← Complex.ofReal_cos,
      show (S:ℂ)-(Real.cos θ:ℂ) = ((S-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
      preferredArccos_ofReal _ hW hW',← Complex.ofReal_sin]
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW')
      (Real.arccos_lt_pi.mpr hW)).ne'
  unfold preferredPhaseCurvature
  exact (by fun_prop : ContinuousAt
    (fun z : ℂ × ℂ => z.1*(1-z.1*Complex.cos z.2+(Complex.cos z.2)^2))
    ((S:ℂ),(θ:ℂ))).div (hsine.pow 3) (pow_ne_zero 3 hsn)

def preferredCompactDirection : ℂ :=
  Complex.exp (-Complex.I*((3*Real.pi/8:ℝ):ℂ))

theorem preferredCompactDirection_re :
    preferredCompactDirection.re = Real.cos (3*Real.pi/8) := by
  simp [preferredCompactDirection,Complex.exp_re,Complex.mul_re,Complex.mul_im,Real.cos_neg]

theorem preferredCompactDirection_re_pos : 0 < preferredCompactDirection.re := by
  rw [preferredCompactDirection_re]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩

def preferredRadialTrace (d : PreferredBranchData) (ε : ℝ) : ℂ :=
  IsingBulk.Branch.radialParameter d.alpha ε+(IsingBulk.Branch.radialParameter d.alpha ε)⁻¹

theorem preferredRadialTrace_zero (d : PreferredBranchData) :
    preferredRadialTrace d 0 = ((1+Real.cos d.b:ℝ):ℂ) := by
  obtain ⟨hr,hi⟩ := IsingBulk.Branch.radial_trace_components d.alpha 0 (by norm_num)
  apply Complex.ext
  · rw [show (preferredRadialTrace d 0).re = _ from hr]
    simp only [Complex.ofReal_re]
    rw [d.angle_relation]
    ring
  · rw [show (preferredRadialTrace d 0).im = _ from hi]
    simp

def preferredBumpAngle (m p : ℝ → ℝ) (τ σ υ θ : ℝ) : ℂ :=
  (θ:ℂ)-Complex.I*(τ:ℂ)*((σ*m θ-υ*p θ:ℝ):ℂ)

def preferredBumpTangent (m' p' : ℝ → ℝ) (τ σ υ θ : ℝ) : ℂ :=
  1-Complex.I*(τ:ℂ)*((σ*m' θ-υ*p' θ:ℝ):ℂ)

def preferredCompactCurvature (d : PreferredBranchData) (m p : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  preferredPhaseCurvature (preferredRadialTrace d ε) (preferredBumpAngle m p τ σ υ θ)

def preferredPhaseSlope (S w : ℂ) : ℂ :=
  -Complex.sin w/Complex.sin (preferredArccos (S-Complex.cos w))

def preferredBumpSecond (m'' p'' : ℝ → ℝ) (τ σ υ θ : ℝ) : ℂ :=
  -Complex.I*(τ:ℂ)*((σ*m'' θ-υ*p'' θ:ℝ):ℂ)

def preferredCompactSlope (d : PreferredBranchData) (m p : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  preferredPhaseSlope (preferredRadialTrace d ε) (preferredBumpAngle m p τ σ υ θ)

/-- Exact complete expression −B'=Q*a²−b*a', including both bump
second derivatives at the fixed occupancies. -/
def preferredCompactTransportCurvature (d : PreferredBranchData)
    (m p m' p' m'' p'' : ℝ → ℝ) (ε τ σ υ θ : ℝ) : ℂ :=
  preferredCompactCurvature d m p ε τ σ υ θ*(preferredBumpTangent m' p' τ σ υ θ)^2-
    preferredCompactSlope d m p ε τ σ υ θ*preferredBumpSecond m'' p'' τ σ υ θ

def preferredCompactProjectedCurvature (d : PreferredBranchData)
    (m p m' p' m'' p'' : ℝ → ℝ) (ε τ σ υ θ : ℝ) : ℝ :=
  (preferredCompactDirection*
    preferredCompactTransportCurvature d m p m' p' m'' p'' ε τ σ υ θ).re


theorem preferredPhaseSlope_continuousAt_real {S θ : ℝ}
    (hW : -1 < S-Real.cos θ) (hW' : S-Real.cos θ < 1) :
    ContinuousAt (fun z : ℂ × ℂ => preferredPhaseSlope z.1 z.2)
      ((S:ℂ),(θ:ℂ)) := by
  have harg : ContinuousAt (fun z : ℂ × ℂ => z.1-Complex.cos z.2)
      ((S:ℂ),(θ:ℂ)) := by fun_prop
  have harc : ContinuousAt (fun z : ℂ × ℂ => preferredArccos (z.1-Complex.cos z.2))
      ((S:ℂ),(θ:ℂ)) :=
    ((preferredArccos_analyticAt_real _ hW hW').continuousAt).comp_of_eq harg
      (by rw [← Complex.ofReal_cos]; push_cast; rfl)
  have hsine := Complex.continuous_sin.continuousAt.comp harc
  have hsn : Complex.sin (preferredArccos ((S:ℂ)-Complex.cos (θ:ℂ))) ≠ 0 := by
    rw [← Complex.ofReal_cos,
      show (S:ℂ)-(Real.cos θ:ℂ) = ((S-Real.cos θ:ℝ):ℂ) by push_cast; rfl,
      preferredArccos_ofReal _ hW hW',← Complex.ofReal_sin]
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW')
      (Real.arccos_lt_pi.mpr hW)).ne'
  unfold preferredPhaseSlope
  exact (by fun_prop : ContinuousAt (fun z : ℂ × ℂ => -Complex.sin z.2)
    ((S:ℂ),(θ:ℂ))).div hsine hsn

/-- Joint continuity of the actual finite-occupancy compact-right source
functions, including the complete corrected curvature. -/
theorem preferredCompact_source_continuousAt_zero (d : PreferredBranchData)
    (m p m' p' m'' p'' : ℝ → ℝ)
    (hm : Continuous m) (hp : Continuous p)
    (hm' : Continuous m') (hp' : Continuous p')
    (hm'' : Continuous m'') (hp'' : Continuous p'')
    {ρ δR θ σ υ : ℝ} (hρ : 0 < ρ) (hδR : δR < d.b)
    (hθ : θ ∈ Set.Icc (-d.b+ρ) δR) :
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredCompactCurvature d m p z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) ∧
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredCompactSlope d m p z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) ∧
    ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredCompactProjectedCurvature d m p m' p' m'' p''
        z.1.1 z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
  obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδR hθ
  let H : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) → ℂ × ℂ := fun z =>
    (preferredRadialTrace d z.1.1,preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1)
  have hH : ContinuousAt H ((0,0),(θ,σ,υ)) := by
    dsimp [H,preferredRadialTrace,preferredBumpAngle,IsingBulk.Branch.radialParameter]
    fun_prop (disch := simp [Complex.exp_ne_zero])
  have hH0 : H ((0,0),(θ,σ,υ)) = (((1+Real.cos d.b:ℝ):ℂ),(θ:ℂ)) := by
    simp [H,preferredRadialTrace_zero,preferredBumpAngle]
  have hQ := (preferredPhaseCurvature_continuousAt_real hW hW').comp_of_eq hH hH0
  have hb := (preferredPhaseSlope_continuousAt_real hW hW').comp_of_eq hH hH0
  refine ⟨hQ,hb,?_⟩
  have ha : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpTangent m' p' z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
    unfold preferredBumpTangent
    fun_prop
  have ha' : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      preferredBumpSecond m'' p'' z.1.2 z.2.2.1 z.2.2.2 z.2.1) ((0,0),(θ,σ,υ)) := by
    unfold preferredBumpSecond
    fun_prop
  exact Complex.continuous_re.continuousAt.comp
    (continuousAt_const.mul ((hQ.mul (ha.pow 2)).sub (hb.mul ha')))

/-- Uniform compact-right G3 and corrected G4 curvature, with the actual
occupancy parameters kept throughout. The constants are derived from the
physical reference dispersion and compactness after the bumps are fixed. -/
theorem preferred_compact_right_transport_curvature (d : PreferredBranchData)
    (m p m' p' m'' p'' : ℝ → ℝ)
    (hm : Continuous m) (hp : Continuous p)
    (hm' : Continuous m') (hp' : Continuous p')
    (hm'' : Continuous m'') (hp'' : Continuous p'')
    {ρ δR : ℝ} (hρ : 0 < ρ) (hδR : δR < d.b) :
    ∃ a B r : ℝ, 0 < a ∧ 0 < B ∧ 0 < r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε| < r → |τ| < r → θ ∈ Set.Icc (-d.b+ρ) δR →
      σ ∈ Set.Icc 0 1 → υ ∈ Set.Icc 0 1 →
      a ≤ (preferredCompactDirection*preferredCompactCurvature d m p ε τ σ υ θ).re ∧
      a ≤ preferredCompactProjectedCurvature d m p m' p' m'' p'' ε τ σ υ θ ∧
      ‖preferredCompactCurvature d m p ε τ σ υ θ‖ ≤ B ∧
      ‖preferredCompactSlope d m p ε τ σ υ θ‖ ≤ B := by
  let K : Set (ℝ × ℝ × ℝ) := Set.Icc (-d.b+ρ) δR ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let Q : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ := fun x y =>
    preferredCompactCurvature d m p x.1 x.2 y.2.1 y.2.2 y.1
  let b : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ := fun x y =>
    preferredCompactSlope d m p x.1 x.2 y.2.1 y.2.2 y.1
  let F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℝ := fun x y =>
    preferredCompactProjectedCurvature d m p m' p' m'' p'' x.1 x.2 y.2.1 y.2.2 y.1
  let S := 1+Real.cos d.b
  let A := S*(1-S^2/4)
  have hS := preferred_reference_trace_range d
  have hA : 0 < A := by
    have hpos : 0 < 1-S^2/4 := by dsimp [S]; nlinarith
    exact mul_pos hS.1 hpos
  let a := preferredCompactDirection.re*A/2
  have ha : 0 < a := div_pos (mul_pos preferredCompactDirection_re_pos hA) (by norm_num)
  have hcont (y : ℝ × ℝ × ℝ) (hy : y ∈ K) :=
    preferredCompact_source_continuousAt_zero d m p m' p' m'' p'' hm hp hm' hp' hm'' hp''
      (σ := y.2.1) (υ := y.2.2) hρ hδR hy.1
  have hnormcont : ContinuousOn (fun y => ‖Q (0,0) y‖+‖b (0,0) y‖) K := by
    intro y hy
    have h : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        ‖Q z.1 z.2‖+‖b z.1 z.2‖) ((0,0),y) := by
      convert! ((hcont y hy).1.norm.add (hcont y hy).2.1.norm) using 1
    exact (h.comp (by fun_prop :
      ContinuousAt (fun y : ℝ × ℝ × ℝ => (((0,0):ℝ × ℝ),y)) y)).continuousWithinAt
  obtain ⟨B₀,hB₀⟩ := hK.exists_bound_of_continuousOn hnormcont
  let B := max B₀ 0+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase (y : ℝ × ℝ × ℝ) (hy : y ∈ K) :
      a < (preferredCompactDirection*Q (0,0) y).re ∧ a < F (0,0) y ∧
      ‖Q (0,0) y‖+‖b (0,0) y‖ < B := by
    obtain ⟨hW,hW'⟩ := preferred_right_reference_margin d hρ hδR hy.1
    obtain ⟨_,he,hlo⟩ := preferred_reference_curvature_lower hS.1 hS.2 hW hW'
    have hQ : Q (0,0) y = preferredPhaseCurvature (S:ℂ) (y.1:ℂ) := by
      simp [Q,preferredCompactCurvature,preferredBumpAngle,preferredRadialTrace_zero,S]
    have hF : F (0,0) y = (preferredCompactDirection*Q (0,0) y).re := by
      simp [F,Q,preferredCompactProjectedCurvature,preferredCompactTransportCurvature,
        preferredBumpTangent,preferredBumpSecond]
    have hQim : (Q (0,0) y).im = 0 := by rw [hQ,he]; rfl
    have hlo' : A ≤ (Q (0,0) y).re := by rw [hQ]; exact hlo
    have hpj : a < (preferredCompactDirection*Q (0,0) y).re := by
      rw [Complex.mul_re,hQim,mul_zero,sub_zero]
      dsimp [a]
      nlinarith [mul_le_mul_of_nonneg_left hlo' preferredCompactDirection_re_pos.le,
        mul_pos preferredCompactDirection_re_pos hA]
    refine ⟨hpj,hF ▸ hpj,?_⟩
    have hh := hB₀ y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
    exact hh.trans_lt (by dsimp [B]; have := le_max_left B₀ 0; linarith)
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ), ∀ y ∈ K,
      a < (preferredCompactDirection*Q x y).re ∧ a < F x y ∧
      ‖Q x y‖+‖b x y‖ < B := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    obtain ⟨hQ,hb,hF⟩ := hcont y hy
    obtain ⟨hq0,hF0,hn0⟩ := hbase y hy
    have hpj := Complex.continuous_re.continuousAt.comp (hQ.const_mul preferredCompactDirection)
    exact (continuousAt_const.eventually_lt hpj hq0).and
      ((continuousAt_const.eventually_lt hF hF0).and
        ((hQ.norm.add hb.norm).eventually_lt continuousAt_const hn0))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨a,B,r,ha,hB,hr,?_⟩
  intro ε τ σ υ θ hε hτ hθ hσ hυ
  have hdist : dist (ε,τ) ((0,0):ℝ × ℝ) < r := by
    change dist (ε,τ) (0:ℝ × ℝ) < r
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ
  obtain ⟨hQ,hF,hn⟩ := hball hdist (θ,σ,υ) ⟨hθ,hσ,hυ⟩
  refine ⟨hQ.le,hF.le,?_,?_⟩
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hn.le
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hn.le


/-! ## Actual moving-center cancellation and physical-parameter jets -/

theorem preferred_sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    Complex.sqrt (z^2) = z := by
  obtain h | h := eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z
    (IsingBulk.Branch.sqrt_sq (z^2))
  · exact h
  · have hn := IsingBulk.Branch.sqrt_re_nonneg_all (z^2)
    rw [h,Complex.neg_re] at hn
    linarith

/-- Exact inverse cosine on the entire vertical physical strip. -/
theorem preferredArccos_cos_strip (z : ℂ) (hz : 0 < z.re) (hzπ : z.re < Real.pi) :
    preferredArccos (Complex.cos z) = z := by
  have hs : 0 < (Complex.sin z).re := by
    rw [Complex.sin_eq]
    simpa [← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh] using
      mul_pos (Real.sin_pos_of_pos_of_lt_pi hz hzπ) (Real.cosh_pos z.im)
  have hsq : 1-(Complex.cos z)^2 = (Complex.sin z)^2 := by
    linear_combination -(Complex.sin_sq_add_cos_sq z)
  have hroot : preferredCosineRoot (Complex.cos z) = Complex.exp (z*Complex.I) := by
    unfold preferredCosineRoot
    rw [hsq,preferred_sqrt_sq_of_re_pos _ hs,Complex.exp_mul_I]
    ring
  unfold preferredArccos
  rw [hroot,Complex.log_exp]
  · ring_nf
    simp [Complex.I_sq]
  · simpa using (show -Real.pi < z.re by linarith [Real.pi_pos])
  · simpa using hzπ.le

def traceMovingBranch (S : ℂ) : ℂ := -preferredArccos (S-1)

def traceMovingInverse (S q : ℂ) : ℂ :=
  complexRightInverse S (q+traceMovingBranch S)

def preferredMovingBranch (s : ℂ) : ℂ := traceMovingBranch (temperatureTrace s)

def preferredMovingInverse (s q : ℂ) : ℂ :=
  traceMovingInverse (temperatureTrace s) q

theorem traceMovingBranch_cos (S : ℂ) :
    Complex.cos (traceMovingBranch S) = S-1 := by
  rw [traceMovingBranch,Complex.cos_neg,cos_preferredArccos]

theorem traceMovingBranch_half_cos (S : ℂ) :
    2*(Complex.cos (traceMovingBranch S/2))^2 = S := by
  have h := Complex.cos_two_mul (traceMovingBranch S/2)
  rw [show 2*(traceMovingBranch S/2) = traceMovingBranch S by ring,traceMovingBranch_cos] at h
  linear_combination -h

theorem traceMovingBranch_half_cos_ne {S : ℂ} (hS : S ≠ 0) :
    Complex.cos (traceMovingBranch S/2) ≠ 0 := by
  intro h
  have hh := traceMovingBranch_half_cos S
  rw [h] at hh
  norm_num at hh
  exact hS hh.symm

/-- The source moving-center identity holds throughout the local branch
strip, not only at the real limiting point. -/
theorem traceMovingInverse_at_zero (S : ℂ) (hS : S ≠ 0)
    (hB : 0 < (preferredArccos (S-1)).re)
    (hB' : (preferredArccos (S-1)).re < 2*Real.pi) :
    traceMovingInverse S 0 = traceMovingBranch S := by
  have hc := traceMovingBranch_half_cos_ne hS
  have harg : S/(2*Complex.cos (traceMovingBranch S/2)) =
      Complex.cos (traceMovingBranch S/2) := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hc)).mpr
    linear_combination -(traceMovingBranch_half_cos S)
  have harc : preferredArccos (Complex.cos (traceMovingBranch S/2)) =
      -traceMovingBranch S/2 := by
    rw [show Complex.cos (traceMovingBranch S/2) =
      Complex.cos (-traceMovingBranch S/2) by rw [show -traceMovingBranch S/2 =
        -(traceMovingBranch S/2) by ring,Complex.cos_neg]]
    apply preferredArccos_cos_strip
    · simp only [traceMovingBranch,neg_neg,Complex.div_ofNat_re]
      linarith
    · simp only [traceMovingBranch,neg_neg,Complex.div_ofNat_re]
      linarith
  unfold traceMovingInverse complexRightInverse
  rw [zero_add,harg,harc]
  ring

theorem traceMovingBranch_sin_ne {S : ℂ} (hS : S ≠ 0) (hS' : S ≠ 2) :
    Complex.sin (traceMovingBranch S) ≠ 0 := by
  intro h
  have hsq := Complex.sin_sq_add_cos_sq (traceMovingBranch S)
  rw [h,traceMovingBranch_cos] at hsq
  have hf : S*(S-2) = 0 := by linear_combination hsq
  obtain hz | hz := mul_eq_zero.mp hf
  · exact hS hz
  · exact hS' (sub_eq_zero.mp hz)

/-- Differentiating the exact dispersion at the moving center forces Uq=0;
no branch-scale estimate is assumed. -/
theorem traceMovingInverse_hasDerivAt_zero (S : ℂ) (hS : S ≠ 0) (hS' : S ≠ 2)
    (hB : 0 < (preferredArccos (S-1)).re)
    (hB' : (preferredArccos (S-1)).re < 2*Real.pi)
    (hU : DifferentiableAt ℂ (complexRightInverse S) (traceMovingBranch S)) :
    HasDerivAt (traceMovingInverse S) 0 0 := by
  let B := traceMovingBranch S
  have hc := traceMovingBranch_half_cos_ne hS
  have hval : complexRightInverse S B = B := by
    simpa only [traceMovingInverse,zero_add] using traceMovingInverse_at_zero S hS hB hB'
  have hd := hU.hasDerivAt.ccos.add (((hasDerivAt_id B).sub hU.hasDerivAt).ccos)
  have hne : ∀ᶠ v in 𝓝 B, Complex.cos (v/2) ≠ 0 :=
    (by fun_prop : ContinuousAt (fun v : ℂ => Complex.cos (v/2)) B).eventually_ne hc
  have heq : (fun v => Complex.cos (complexRightInverse S v)+
      Complex.cos (v-complexRightInverse S v)) =ᶠ[𝓝 B] (fun _ => S) := by
    filter_upwards [hne] with v hv
    exact complexRightInverse_dispersion S v hv
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const B S)
  simp only [Pi.sub_apply,id_eq] at he
  rw [hval,sub_self,Complex.sin_zero] at he
  have hder : deriv (complexRightInverse S) B = 0 := by
    have hh : Complex.sin B * deriv (complexRightInverse S) B = 0 := by
      simpa using congrArg Neg.neg he
    exact (mul_eq_zero.mp hh).resolve_left (traceMovingBranch_sin_ne hS hS')
  have hcalc := hU.hasDerivAt.comp_of_eq 0 ((hasDerivAt_id (0:ℂ)).add_const B)
    (by simp [B])
  have hd0 : deriv (complexRightInverse S) (traceMovingBranch S) = 0 := hder
  rw [hd0,zero_mul] at hcalc
  convert! hcalc using 1


theorem traceMovingBranch_reference (d : PreferredBranchData) :
    traceMovingBranch ((1+Real.cos d.b:ℝ):ℂ) = -(d.b:ℂ) := by
  unfold traceMovingBranch
  rw [show (((1+Real.cos d.b:ℝ):ℂ)-1) = (Real.cos d.b:ℂ) by push_cast; ring,
    preferredArccos_cos d.b d.b_pos d.b_lt]

theorem traceMovingBranch_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ traceMovingBranch (((1+Real.cos d.b:ℝ):ℂ)) := by
  obtain ⟨hS,hS'⟩ := preferred_reference_trace_range d
  have ha := preferredArccos_analyticAt_real (Real.cos d.b) (by linarith) (by linarith)
  exact (ha.comp_of_eq (analyticAt_id.sub analyticAt_const)
    (by simp only [Pi.sub_apply,id_eq]; push_cast; ring)).neg

theorem complexRightInverse_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => complexRightInverse z.1 z.2)
      (((1+Real.cos d.b:ℝ):ℂ),-(d.b:ℂ)) := by
  obtain ⟨hS,_⟩ := preferred_reference_trace_range d
  have hc : 0 < Real.cos (-d.b/2) := by
    rw [show -d.b/2 = -(d.b/2) by ring,Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [d.b_pos,Real.pi_pos],by linarith [d.b_lt]⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt
  have hh := Real.cos_two_mul (d.b/2)
  rw [show 2*(d.b/2)=d.b by ring] at hh
  have hD : 0 < inverseDiscriminant (1+Real.cos d.b) (-d.b) := by
    unfold inverseDiscriminant
    rw [show -d.b/2 = -(d.b/2) by ring,Real.cos_neg]
    nlinarith [Real.sin_sq_add_cos_sq d.b]
  simpa only [Complex.ofReal_neg] using
    complexRightInverse_analyticAt_real (1+Real.cos d.b) (-d.b) hS hc hD

theorem traceMovingInverse_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => traceMovingInverse z.1 z.2)
      (((1+Real.cos d.b:ℝ):ℂ),0) := by
  have hB : AnalyticAt ℂ (fun z : ℂ × ℂ => traceMovingBranch z.1)
      ((((1+Real.cos d.b:ℝ):ℂ)),(0:ℂ)) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := traceMovingBranch)
      (traceMovingBranch_analyticAt_reference d) analyticAt_fst
  exact (complexRightInverse_analyticAt_reference d).comp_of_eq
    (analyticAt_fst.prod (analyticAt_snd.add hB)) (by
      apply Prod.ext
      · rfl
      · change 0+traceMovingBranch (((1+Real.cos d.b:ℝ):ℂ)) = -(d.b:ℂ)
        rw [zero_add,traceMovingBranch_reference])

/-- Both moving-center identities hold on one complex parameter neighborhood.
This is the source cancellation needed before estimating any parameter jets. -/
theorem traceMovingInverse_center_germ (d : PreferredBranchData) :
    ∀ᶠ S in 𝓝 (((1+Real.cos d.b:ℝ):ℂ)),
      traceMovingInverse S 0 = traceMovingBranch S ∧
        deriv (traceMovingInverse S) 0 = 0 := by
  let S₀ : ℂ := ((1+Real.cos d.b:ℝ):ℂ)
  obtain ⟨hS₀,hS₀'⟩ := preferred_reference_trace_range d
  have hS : S₀ ≠ 0 := by dsimp [S₀]; exact_mod_cast hS₀.ne'
  have hS' : S₀ ≠ 2 := by dsimp [S₀]; exact_mod_cast hS₀'.ne
  have hB := traceMovingBranch_analyticAt_reference d
  have hArc : ContinuousAt (fun S : ℂ => preferredArccos (S-1)) S₀ := by
    have hfun : -traceMovingBranch = fun S => preferredArccos (S-1) := by
      funext S
      simp [traceMovingBranch]
    rw [← hfun]
    exact hB.neg.continuousAt
  have hArc0 : preferredArccos (S₀-1) = (d.b:ℂ) := by
    dsimp [S₀]
    rw [show (((1+Real.cos d.b:ℝ):ℂ)-1) = (Real.cos d.b:ℂ) by push_cast; ring]
    exact preferredArccos_cos d.b d.b_pos d.b_lt
  have hArcre : ContinuousAt (fun S : ℂ => (preferredArccos (S-1)).re) S₀ :=
    Complex.continuous_re.continuousAt.comp hArc
  have hArclo := (continuousAt_const : ContinuousAt (fun _ : ℂ => (0:ℝ)) S₀).eventually_lt hArcre
    (by rw [hArc0]; exact d.b_pos)
  have hArchi := hArcre.eventually_lt
    (continuousAt_const : ContinuousAt (fun _ : ℂ => 2*Real.pi) S₀)
    (by rw [hArc0]; exact (show d.b < 2*Real.pi by linarith [d.b_lt,Real.pi_pos]))
  have hmap : ContinuousAt (fun S : ℂ => (S,traceMovingBranch S)) S₀ :=
    continuousAt_id.prodMk hB.continuousAt
  have hmapt : Filter.Tendsto (fun S : ℂ => (S,traceMovingBranch S)) (𝓝 S₀)
      (𝓝 (S₀,-(d.b:ℂ))) := by
    simpa only [S₀,traceMovingBranch_reference] using hmap.tendsto
  have hraw := hmapt.eventually (complexRightInverse_analyticAt_reference d).eventually_analyticAt
  filter_upwards [continuousAt_id.eventually_ne hS,continuousAt_id.eventually_ne hS',
    hArclo,hArchi,hraw] with S hS hS' hB hB' hraw
  have hU : DifferentiableAt ℂ (complexRightInverse S) (traceMovingBranch S) :=
    (hraw.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact ⟨traceMovingInverse_at_zero S hS hB hB',
    (traceMovingInverse_hasDerivAt_zero S hS hS' hB hB' hU).deriv⟩

/-- Every fixed parameter derivative of Uq vanishes at the branch center. -/
theorem traceMovingInverse_parameter_center_jet (d : PreferredBranchData) (a : ℕ) :
    iteratedDeriv a (fun S : ℂ => deriv (traceMovingInverse S) 0)
      (((1+Real.cos d.b:ℝ):ℂ)) = 0 := by
  have hz : (fun S : ℂ => deriv (traceMovingInverse S) 0) =ᶠ[
      𝓝 (((1+Real.cos d.b:ℝ):ℂ))] (fun _ => (0:ℂ)) :=
    (traceMovingInverse_center_germ d).mono (fun _ h => h.2)
  rw [hz.iteratedDeriv_eq a]
  simp


/-- Genuine q-then-parameter partial derivatives of the explicit moving
inverse, represented by fixed coordinate directions. -/
def regularParameterQJet : ℕ → (ℂ × ℂ → ℂ)
  | 0 => fun z => fderiv ℂ (fun p : ℂ × ℂ => traceMovingInverse p.1 p.2) z (0,1)
  | n+1 => fun z => fderiv ℂ (regularParameterQJet n) z (1,0)

theorem regularParameterQJet_analyticAt (n : ℕ) (z : ℂ × ℂ)
    (hU : AnalyticAt ℂ (fun p : ℂ × ℂ => traceMovingInverse p.1 p.2) z) :
    AnalyticAt ℂ (regularParameterQJet n) z := by
  induction n with
  | zero => exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):ℂ × ℂ)).analyticAt _).comp hU.fderiv
  | succ n ih => exact ((ContinuousLinearMap.apply ℂ ℂ ((1,0):ℂ × ℂ)).analyticAt _).comp ih.fderiv

theorem regularParameterQJet_eq_iteratedDeriv (n : ℕ) (S q : ℂ)
    (hU : AnalyticAt ℂ (fun p : ℂ × ℂ => traceMovingInverse p.1 p.2) (S,q)) :
    regularParameterQJet n (S,q) =
      iteratedDeriv n (fun t => deriv (traceMovingInverse t) q) S := by
  induction n generalizing S with
  | zero =>
    have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_const q S).prodMk (hasDerivAt_id q))
    simpa only [regularParameterQJet,iteratedDeriv_zero,Function.comp_def] using hd.deriv.symm
  | succ n ih =>
    have hJ := regularParameterQJet_analyticAt n (S,q) hU
    have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt S
      ((hasDerivAt_id S).prodMk (hasDerivAt_const S q))
    have ht : Filter.Tendsto (fun t : ℂ => (t,q)) (𝓝 S) (𝓝 (S,q)) :=
      (show Continuous (fun t : ℂ => (t,q)) by fun_prop).tendsto S
    have hg : (fun t => regularParameterQJet n (t,q)) =ᶠ[𝓝 S]
        iteratedDeriv n (fun t => deriv (traceMovingInverse t) q) := by
      filter_upwards [ht.eventually hU.eventually_analyticAt] with t ht
      exact ih t ht
    calc
      _ = deriv (fun t => regularParameterQJet n (t,q)) S := by
        simpa only [regularParameterQJet,Function.comp_def,id_eq] using hd.deriv.symm
      _ = deriv (iteratedDeriv n (fun t => deriv (traceMovingInverse t) q)) S := hg.deriv_eq
      _ = _ := by rw [iteratedDeriv_succ]

/-- All parameter jets vanish along q=0 on a common germ for each fixed order. -/
theorem regularParameterQJet_center_germ (d : PreferredBranchData) (n : ℕ) :
    ∀ᶠ S in 𝓝 (((1+Real.cos d.b:ℝ):ℂ)), regularParameterQJet n (S,0) = 0 := by
  let S₀ : ℂ := ((1+Real.cos d.b:ℝ):ℂ)
  have hU := traceMovingInverse_analyticAt_reference d
  have ht : Filter.Tendsto (fun S : ℂ => (S,(0:ℂ))) (𝓝 S₀) (𝓝 (S₀,0)) :=
    (show Continuous (fun S : ℂ => (S,(0:ℂ))) by fun_prop).tendsto S₀
  have hUa := ht.eventually hU.eventually_analyticAt
  induction n with
  | zero =>
    filter_upwards [hUa,traceMovingInverse_center_germ d] with S hU hz
    rw [regularParameterQJet_eq_iteratedDeriv 0 S 0 hU,iteratedDeriv_zero]
    exact hz.2
  | succ n ih =>
    have hJa := ht.eventually (regularParameterQJet_analyticAt n (S₀,0) hU).eventually_analyticAt
    filter_upwards [hJa,ih.eventually_nhds] with S hJ hz
    have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt S
      ((hasDerivAt_id S).prodMk (hasDerivAt_const S (0:ℂ)))
    have hzero : HasDerivAt (fun t => regularParameterQJet n (t,0)) 0 S :=
      (hasDerivAt_const S (0:ℂ)).congr_of_eventuallyEq hz
    exact hd.unique hzero

/-- Analyticity plus actual axis vanishing gives a uniform first-order
factor in q; no epsilon or radial scale is introduced. -/
theorem preferred_analytic_axis_bound (F : ℂ × ℂ → ℂ) (S₀ : ℂ)
    (hF : AnalyticAt ℂ F (S₀,0))
    (hz : ∀ᶠ S in 𝓝 S₀, F (S,0) = 0) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ S q : ℂ,
      ‖S-S₀‖ < r → ‖q‖ < r → ‖F (S,q)‖ ≤ C*‖q‖ := by
  obtain ⟨K,U,hU,hLip⟩ := hF.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r₁,hr₁,hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r₂,hr₂,hzero⟩ := Metric.eventually_nhds_iff.mp hz
  let r := min r₁ r₂
  refine ⟨(K:ℝ)+1,r,by positivity,lt_min hr₁ hr₂,?_⟩
  intro S q hS hq
  have hS₁ := hS.trans_le (min_le_left r₁ r₂)
  have hq₁ := hq.trans_le (min_le_left r₁ r₂)
  have hS₂ := hS.trans_le (min_le_right r₁ r₂)
  have hzS := hzero (by simpa only [dist_eq_norm] using hS₂)
  have hx : (S,q) ∈ U := hball (by
    simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      sub_zero,max_lt_iff] using And.intro hS₁ hq₁)
  have hx₀ : (S,(0:ℂ)) ∈ U := hball (by
    simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      sub_self,norm_zero,max_lt_iff] using And.intro hS₁ hr₁)
  have hh := hLip.dist_le_mul (S,q) hx (S,(0:ℂ)) hx₀
  rw [hzS,dist_zero_right] at hh
  have hdist : dist (S,q) (S,(0:ℂ)) = ‖q‖ := by simp [Prod.dist_eq,dist_self]
  rw [hdist] at hh
  exact hh.trans (by nlinarith [norm_nonneg q])

/-- Local source form of (7.16), for every actual mixed parameter jet. -/
theorem preferred_moving_inverse_parameter_q_bound (d : PreferredBranchData) (n : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ S q : ℂ,
      ‖S-(((1+Real.cos d.b:ℝ):ℂ))‖ < r → ‖q‖ < r →
      ‖regularParameterQJet n (S,q)‖ ≤ C*‖q‖ :=
  preferred_analytic_axis_bound _ _
    (regularParameterQJet_analyticAt n _ (traceMovingInverse_analyticAt_reference d))
    (regularParameterQJet_center_germ d n)


def preferredSelectedPoint (d : PreferredBranchData) : ℂ :=
  IsingBulk.Branch.radialParameter d.alpha 0

theorem preferredSelectedPoint_ne_zero (d : PreferredBranchData) :
    preferredSelectedPoint d ≠ 0 := by
  simp [preferredSelectedPoint,IsingBulk.Branch.radialParameter,Complex.exp_ne_zero]

theorem temperatureTrace_preferredSelectedPoint (d : PreferredBranchData) :
    temperatureTrace (preferredSelectedPoint d) = (((1+Real.cos d.b:ℝ):ℂ)) :=
  preferredRadialTrace_zero d

set_option maxHeartbeats 800000 in
theorem preferredMovingInverse_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (preferredSelectedPoint d,0) := by
  have htrace : AnalyticAt ℂ temperatureTrace (preferredSelectedPoint d) := by
    unfold temperatureTrace
    exact analyticAt_id.add (analyticAt_id.inv (preferredSelectedPoint_ne_zero d))
  have htraceF : AnalyticAt ℂ (fun z : ℂ × ℂ => temperatureTrace z.1)
      (preferredSelectedPoint d,(0:ℂ)) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := temperatureTrace) htrace analyticAt_fst
  change AnalyticAt ℂ (fun z : ℂ × ℂ => traceMovingInverse (temperatureTrace z.1) z.2)
    (preferredSelectedPoint d,(0:ℂ))
  exact AnalyticAt.comp_of_eq
    (f := fun z : ℂ × ℂ => (temperatureTrace z.1,z.2))
    (g := fun z : ℂ × ℂ => traceMovingInverse z.1 z.2)
    (traceMovingInverse_analyticAt_reference d) (htraceF.prod analyticAt_snd)
    (by apply Prod.ext; exact temperatureTrace_preferredSelectedPoint d; rfl)

theorem preferredMovingInverse_center_germ (d : PreferredBranchData) :
    ∀ᶠ s in 𝓝 (preferredSelectedPoint d),
      preferredMovingInverse s 0 = preferredMovingBranch s ∧
        deriv (preferredMovingInverse s) 0 = 0 := by
  have htrace : ContinuousAt temperatureTrace (preferredSelectedPoint d) := by
    unfold temperatureTrace
    fun_prop (disch := exact preferredSelectedPoint_ne_zero d)
  have ht : Filter.Tendsto temperatureTrace (𝓝 (preferredSelectedPoint d))
      (𝓝 (((1+Real.cos d.b:ℝ):ℂ))) := by
    simpa only [temperatureTrace_preferredSelectedPoint] using htrace.tendsto
  exact ht.eventually (traceMovingInverse_center_germ d)

/-- The literal physical-parameter s jets, not surrogate radial labels. -/
def preferredParameterQJet : ℕ → (ℂ × ℂ → ℂ)
  | 0 => fun z => fderiv ℂ (fun p : ℂ × ℂ => preferredMovingInverse p.1 p.2) z (0,1)
  | n+1 => fun z => fderiv ℂ (preferredParameterQJet n) z (1,0)

theorem preferredParameterQJet_analyticAt (n : ℕ) (z : ℂ × ℂ)
    (hU : AnalyticAt ℂ (fun p : ℂ × ℂ => preferredMovingInverse p.1 p.2) z) :
    AnalyticAt ℂ (preferredParameterQJet n) z := by
  induction n with
  | zero => exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):ℂ × ℂ)).analyticAt _).comp hU.fderiv
  | succ n ih => exact ((ContinuousLinearMap.apply ℂ ℂ ((1,0):ℂ × ℂ)).analyticAt _).comp ih.fderiv

theorem preferredParameterQJet_eq_iteratedDeriv (n : ℕ) (s q : ℂ)
    (hU : AnalyticAt ℂ (fun p : ℂ × ℂ => preferredMovingInverse p.1 p.2) (s,q)) :
    preferredParameterQJet n (s,q) =
      iteratedDeriv n (fun t => deriv (preferredMovingInverse t) q) s := by
  induction n generalizing s with
  | zero =>
    have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_const q s).prodMk (hasDerivAt_id q))
    simpa only [preferredParameterQJet,iteratedDeriv_zero,Function.comp_def] using hd.deriv.symm
  | succ n ih =>
    have hJ := preferredParameterQJet_analyticAt n (s,q) hU
    have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s q))
    have ht : Filter.Tendsto (fun t : ℂ => (t,q)) (𝓝 s) (𝓝 (s,q)) :=
      (show Continuous (fun t : ℂ => (t,q)) by fun_prop).tendsto s
    have hg : (fun t => preferredParameterQJet n (t,q)) =ᶠ[𝓝 s]
        iteratedDeriv n (fun t => deriv (preferredMovingInverse t) q) := by
      filter_upwards [ht.eventually hU.eventually_analyticAt] with t ht
      exact ih t ht
    calc
      _ = deriv (fun t => preferredParameterQJet n (t,q)) s := by
        simpa only [preferredParameterQJet,Function.comp_def,id_eq] using hd.deriv.symm
      _ = deriv (iteratedDeriv n (fun t => deriv (preferredMovingInverse t) q)) s := hg.deriv_eq
      _ = _ := by rw [iteratedDeriv_succ]

theorem preferredParameterQJet_center_germ (d : PreferredBranchData) (n : ℕ) :
    ∀ᶠ s in 𝓝 (preferredSelectedPoint d), preferredParameterQJet n (s,0) = 0 := by
  have hU := preferredMovingInverse_analyticAt_reference d
  have ht : Filter.Tendsto (fun s : ℂ => (s,(0:ℂ)))
      (𝓝 (preferredSelectedPoint d)) (𝓝 (preferredSelectedPoint d,0)) :=
    (show Continuous (fun s : ℂ => (s,(0:ℂ))) by fun_prop).tendsto (preferredSelectedPoint d)
  have hUa := ht.eventually hU.eventually_analyticAt
  induction n with
  | zero =>
    filter_upwards [hUa,preferredMovingInverse_center_germ d] with s hU hz
    rw [preferredParameterQJet_eq_iteratedDeriv 0 s 0 hU,iteratedDeriv_zero]
    exact hz.2
  | succ n ih =>
    have hJa := ht.eventually
      (preferredParameterQJet_analyticAt n (preferredSelectedPoint d,0) hU).eventually_analyticAt
    filter_upwards [hJa,ih.eventually_nhds] with s hJ hz
    have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s (0:ℂ)))
    have hzero : HasDerivAt (fun t => preferredParameterQJet n (t,0)) 0 s :=
      (hasDerivAt_const s (0:ℂ)).congr_of_eventuallyEq hz
    exact hd.unique hzero

/-- Source (7.16) near the branch, for genuine parameter derivatives of every
fixed order, uniform in the complex physical parameter and inverse coordinate. -/
theorem preferred_physical_parameter_q_bound (d : PreferredBranchData) (n : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ s q : ℂ,
      ‖s-preferredSelectedPoint d‖ < r → ‖q‖ < r →
      ‖preferredParameterQJet n (s,q)‖ ≤ C*‖q‖ :=
  preferred_analytic_axis_bound _ _
    (preferredParameterQJet_analyticAt n _ (preferredMovingInverse_analyticAt_reference d))
    (preferredParameterQJet_center_germ d n)



/-! ## Genuine pair jets and the complete one-sided inverse identity -/

/-- Exact inverse identity on the physical half-difference strip, including
complex left and right points. It is the branch-specific reverse direction
of the dispersion identity for the literal explicit inverse. -/
theorem complexRightInverse_inverse (S w φ : ℂ)
    (hdisp : Complex.cos w+Complex.cos φ=S)
    (hc : Complex.cos ((w+φ)/2) ≠ 0)
    (hstrip : 0 < ((φ-w)/2).re) (hstrip' : ((φ-w)/2).re < Real.pi) :
    complexRightInverse S (w+φ) = w := by
  have hsum : S=2*Complex.cos ((w+φ)/2)*Complex.cos ((φ-w)/2) := by
    calc
      S=Complex.cos φ+Complex.cos w := by rw [← hdisp]; ring
      _=2*Complex.cos ((φ+w)/2)*Complex.cos ((φ-w)/2) := Complex.cos_add_cos φ w
      _=_ := by rw [add_comm φ w]
  have hquot : S/(2*Complex.cos ((w+φ)/2))=Complex.cos ((φ-w)/2) := by
    rw [hsum]
    field_simp
  rw [complexRightInverse,hquot,preferredArccos_cos_strip _ hstrip hstrip']
  ring

/-- Applying the physical phase and moving-center coordinate recovers the
same deformed angle whenever the explicit physical strip margins hold. -/
theorem preferredMovingInverse_inverse (s w : ℂ)
    (hc : Complex.cos ((w+preferredArccos (temperatureTrace s-Complex.cos w))/2) ≠ 0)
    (hstrip : 0 < ((preferredArccos (temperatureTrace s-Complex.cos w)-w)/2).re)
    (hstrip' : ((preferredArccos (temperatureTrace s-Complex.cos w)-w)/2).re < Real.pi) :
    preferredMovingInverse s
      (preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s) = w := by
  unfold preferredMovingInverse traceMovingInverse preferredMovingBranch
  rw [sub_add_cancel]
  rw [add_comm]
  apply complexRightInverse_inverse _ _ _ ?_ hc hstrip hstrip'
  rw [cos_preferredArccos]
  ring

/-- Source (7.16) in literal iterated-derivative notation, for the actual
complex physical parameter rather than the temperature trace. -/
theorem preferred_physical_parameter_q_deriv_bound (d : PreferredBranchData) (n : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ s q : ℂ,
      ‖s-preferredSelectedPoint d‖ < r → ‖q‖ < r →
      ‖iteratedDeriv n (fun t => deriv (preferredMovingInverse t) q) s‖ ≤ C*‖q‖ := by
  obtain ⟨C,r,hC,hr,hbound⟩ := preferred_physical_parameter_q_bound d n
  have he := (preferredMovingInverse_analyticAt_reference d).eventually_analyticAt
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C,min r R,hC,lt_min hr hR,?_⟩
  intro s q hs hq
  have hdist : dist (s,q) (preferredSelectedPoint d,(0:ℂ)) < R := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [dist_eq_norm] using hs.trans_le (min_le_right r R))
      (by simpa only [dist_zero_right] using hq.trans_le (min_le_right r R))
  rw [← preferredParameterQJet_eq_iteratedDeriv n s q (hball hdist)]
  exact hbound s q (hs.trans_le (min_le_left r R)) (hq.trans_le (min_le_left r R))


def preferredParameterUJet : ℕ → (ℂ × ℂ → ℂ)
  | 0 => fun z => preferredMovingInverse z.1 z.2
  | n+1 => fun z => fderiv ℂ (preferredParameterUJet n) z (1,0)

theorem preferredParameterUJet_analyticAt (n : ℕ) (z : ℂ × ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) z) :
    AnalyticAt ℂ (preferredParameterUJet n) z := by
  induction n with
  | zero => exact hU
  | succ n ih =>
    exact ((ContinuousLinearMap.apply ℂ ℂ ((1,0):ℂ × ℂ)).analyticAt _).comp ih.fderiv

theorem preferredParameterUJet_eq_iteratedDeriv (n : ℕ) (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    preferredParameterUJet n (s,q) = iteratedDeriv n (fun t => preferredMovingInverse t q) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hJ := preferredParameterUJet_analyticAt n (s,q) hU
    have hd := hJ.differentiableAt.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s q))
    have ht : Filter.Tendsto (fun t : ℂ => (t,q)) (𝓝 s) (𝓝 (s,q)) :=
      (show Continuous (fun t : ℂ => (t,q)) by fun_prop).tendsto s
    have hg : (fun t => preferredParameterUJet n (t,q)) =ᶠ[𝓝 s]
        iteratedDeriv n (fun t => preferredMovingInverse t q) := by
      filter_upwards [ht.eventually hU.eventually_analyticAt] with t ht
      exact ih t ht
    calc
      _ = deriv (fun t => preferredParameterUJet n (t,q)) s := by
        simpa only [preferredParameterUJet,Function.comp_def,id_eq] using hd.deriv.symm
      _ = deriv (iteratedDeriv n (fun t => preferredMovingInverse t q)) s := hg.deriv_eq
      _ = _ := by rw [iteratedDeriv_succ]

/-- Genuine q/s derivative commutation, proved by analytic second-derivative
symmetry for the actual inverse. -/
theorem preferredParameterUJet_q_fderiv (n : ℕ) (z : ℂ × ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) z) :
    fderiv ℂ (preferredParameterUJet n) z (0,1) = preferredParameterQJet n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hJ := preferredParameterUJet_analyticAt n z hU
    have heq : (fun x => fderiv ℂ (preferredParameterUJet n) x (0,1)) =ᶠ[𝓝 z]
        preferredParameterQJet n := by
      filter_upwards [hU.eventually_analyticAt] with x hx
      exact ih x hx
    have hsym : fderiv ℂ (fun x => fderiv ℂ (preferredParameterUJet n) x (1,0)) z (0,1) =
        fderiv ℂ (fun x => fderiv ℂ (preferredParameterUJet n) x (0,1)) z (1,0) := by
      simp only [fderiv_clm_apply hJ.fderiv.differentiableAt (differentiableAt_const _),
        fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
      exact hJ.contDiffAt.isSymmSndFDerivAt_of_omega (0,1) (1,0)
    exact hsym.trans (congrArg (fun D : (ℂ × ℂ) →L[ℂ] ℂ => D (1,0)) heq.fderiv_eq)

theorem preferredParameterUJet_hasDerivAt_q (n : ℕ) (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    HasDerivAt (fun v => preferredParameterUJet n (s,v)) (preferredParameterQJet n (s,q)) q := by
  have hd := (preferredParameterUJet_analyticAt n (s,q) hU).differentiableAt.hasFDerivAt.comp_hasDerivAt q
    ((hasDerivAt_const q s).prodMk (hasDerivAt_id q))
  rw [preferredParameterUJet_q_fderiv n (s,q) hU] at hd
  convert! hd using 1

/-- Local source (7.17): every actual physical-parameter jet of a pair
inverse difference retains both the q difference and the maximum q size.
The constant and radius do not depend on the outward approach epsilon. -/
theorem preferred_physical_parameter_pair_bound (d : PreferredBranchData) (n : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ s q₁ q₂ : ℂ,
      ‖s-preferredSelectedPoint d‖ < r → ‖q₁‖ < r → ‖q₂‖ < r →
      ‖iteratedDeriv n (fun t => preferredMovingInverse t q₁-preferredMovingInverse t q₂) s‖ ≤
        C*max ‖q₁‖ ‖q₂‖*‖q₁-q₂‖ := by
  obtain ⟨C,r,hC,hr,hbound⟩ := preferred_physical_parameter_q_bound d n
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp
    (preferredMovingInverse_analyticAt_reference d).eventually_analyticAt
  refine ⟨C,min r R,hC,lt_min hr hR,?_⟩
  intro s q₁ q₂ hs hq₁ hq₂
  have ha (q : ℂ) (hq : ‖q‖ < min r R) :
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) := by
    apply hball
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [dist_eq_norm] using hs.trans_le (min_le_right r R))
      (by simpa only [dist_zero_right] using hq.trans_le (min_le_right r R))
  let B := max ‖q₁‖ ‖q₂‖
  have hB : B < min r R := max_lt hq₁ hq₂
  have hder (q : ℂ) (hq : q ∈ Metric.closedBall (0:ℂ) B) :
      HasDerivWithinAt (fun v => preferredParameterUJet n (s,v))
        (preferredParameterQJet n (s,q)) (Metric.closedBall (0:ℂ) B) q :=
    (preferredParameterUJet_hasDerivAt_q n s q (ha q
      ((by simpa only [Metric.mem_closedBall,dist_zero_right] using hq : ‖q‖ ≤ B).trans_lt hB))).hasDerivWithinAt
  have hderbound (q : ℂ) (hq : q ∈ Metric.closedBall (0:ℂ) B) :
      ‖preferredParameterQJet n (s,q)‖ ≤ C*B := by
    have hqB : ‖q‖ ≤ B := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq
    exact (hbound s q (hs.trans_le (min_le_left r R))
      (hqB.trans_lt (hB.trans_le (min_le_left r R)))).trans
      (mul_le_mul_of_nonneg_left hqB hC.le)
  have hmv := (convex_closedBall (0:ℂ) B).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hderbound (by simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_right ‖q₁‖ ‖q₂‖)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_left ‖q₁‖ ‖q₂‖)
  have hp₁ : AnalyticAt ℂ (fun t : ℂ => (t,q₁)) s := analyticAt_id.prod analyticAt_const
  have hp₂ : AnalyticAt ℂ (fun t : ℂ => (t,q₂)) s := analyticAt_id.prod analyticAt_const
  have ha₁ : AnalyticAt ℂ (fun t => preferredMovingInverse t q₁) s :=
    AnalyticAt.comp (f := fun t : ℂ => (t,q₁))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (ha q₁ hq₁) hp₁
  have ha₂ : AnalyticAt ℂ (fun t => preferredMovingInverse t q₂) s :=
    AnalyticAt.comp (f := fun t : ℂ => (t,q₂))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (ha q₂ hq₂) hp₂
  rw [iteratedDeriv_fun_sub (ha₁.contDiffAt (n := n)) (ha₂.contDiffAt (n := n))]
  rw [← preferredParameterUJet_eq_iteratedDeriv n s q₁ (ha q₁ hq₁),
    ← preferredParameterUJet_eq_iteratedDeriv n s q₂ (ha q₂ hq₂)]
  exact hmv

/-- The literal phase exponential is the physical root on the entire upper
W half-plane, including the compact right arc where Re W can be negative. -/
theorem preferredArccos_physical_upper (W : ℂ) (him : 0 < W.im) :
    Complex.exp (-Complex.I*preferredArccos W) = physicalRoot W := by
  rw [preferred_exp_phase_inverse]
  apply root_unique_in_disk (W := W)
  · simpa only [inv_inv,add_comm] using preferredCosineRoot_trace W
  · exact physicalRoot_trace W
  · exact inv_ne_zero (preferredCosineRoot_ne_zero W)
  · exact physicalRoot_ne_zero W
  · rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ (IsingBulk.Branch.inverseCosineRoot_norm_of_upper him)
  · exact physicalRoot_inside (Or.inl him.ne')

theorem preferred_cosine_realpart (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re*Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [← Complex.ofReal_cos,← Complex.ofReal_sin,← Complex.ofReal_cosh,← Complex.ofReal_sinh]

/-- The fixed half-difference strip on the entire lifted one-sided contour.
The primitive assumptions are the actual upper physical W-domain and fixed
endpoint trace margins, not an inverse-chart conclusion. -/
theorem preferred_half_difference_strip (S w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < S.re) (hSδ : S.re < 2*Real.cos δ)
    (hθlo : -Real.pi-δ ≤ w.re) (hθhi : w.re ≤ δ)
    (hW : 0 < (S-Complex.cos w).im) :
    0 < ((preferredArccos (S-Complex.cos w)-w)/2).re ∧
      ((preferredArccos (S-Complex.cos w)-w)/2).re < Real.pi := by
  let W := S-Complex.cos w
  let φ := preferredArccos W
  have hsheet := IsingBulk.Branch.lowerArccos_sheet_of_upper hW
  change Complex.cos φ = W ∧ 0 < φ.re ∧ φ.re < Real.pi ∧ φ.im < 0 at hsheet
  obtain ⟨hcos,hφ0,hφπ,_⟩ := hsheet
  have hWre : W.re = S.re-Real.cos w.re*Real.cosh w.im := by
    simp only [W,Complex.sub_re,preferred_cosine_realpart]
  have hφre : W.re = Real.cos φ.re*Real.cosh φ.im := by
    rw [← hcos,preferred_cosine_realpart]
  have hlower : w.re < φ.re := by
    by_cases hθ : w.re < 0
    · linarith
    have hθ0 : 0 ≤ w.re := le_of_not_gt hθ
    by_contra hn
    have hφθ : φ.re ≤ w.re := le_of_not_gt hn
    have hcθ : 0 ≤ Real.cos w.re :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
    have hcφθ := Real.cos_le_cos_of_nonneg_of_le_pi hφ0.le (by linarith [Real.pi_pos]) hφθ
    have hcδθ := Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθhi
    have hcφ : 0 ≤ Real.cos φ.re := hcθ.trans hcφθ
    have hmφ := mul_le_mul_of_nonneg_left (Real.one_le_cosh φ.im) hcφ
    have hmθ := mul_le_mul_of_nonneg_left (Real.one_le_cosh w.im) hcθ
    nlinarith
  have hupper : φ.re-w.re < 2*Real.pi := by
    by_cases hθ : -(Real.pi/2) ≤ w.re
    · linarith [Real.pi_pos]
    have hcθ : Real.cos w.re ≤ 0 := by
      have hh := Real.cos_nonpos_of_pi_div_two_le_of_le
        (x := -w.re) (by linarith) (by linarith)
      simpa only [Real.cos_neg] using hh
    have hWr : 0 < W.re := by
      have hh := mul_nonpos_of_nonpos_of_nonneg hcθ (Real.cosh_pos w.im).le
      linarith
    have hφhalf : φ.re < Real.pi/2 := by
      by_contra hn
      have hcφ := Real.cos_nonpos_of_pi_div_two_le_of_le
        (x := φ.re) (le_of_not_gt hn) (by linarith [Real.pi_pos])
      have hh := mul_nonpos_of_nonpos_of_nonneg hcφ (Real.cosh_pos φ.im).le
      linarith
    linarith
  change 0 < ((φ-w)/2).re ∧ ((φ-w)/2).re < Real.pi
  simp only [Complex.div_ofNat_re,Complex.sub_re]
  constructor <;> linarith

/-- The explicit source inverse recovers every angle on the complete lifted
one-sided interval. Its use is not confined to a small branch neighborhood. -/
theorem preferred_global_one_sided_inverse (s w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθlo : -Real.pi-δ ≤ w.re) (hθhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace s-Complex.cos w).im) :
    preferredMovingInverse s
      (preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s) = w := by
  obtain ⟨hl,hu⟩ := preferred_half_difference_strip (temperatureTrace s) w δ
    hδ hδπ hS hSδ hθlo hθhi hW
  apply preferredMovingInverse_inverse s w ?_ hl hu
  intro hc
  have hh := Complex.cos_add_cos w (preferredArccos (temperatureTrace s-Complex.cos w))
  rw [hc,mul_zero,zero_mul,cos_preferredArccos] at hh
  have hz : temperatureTrace s = 0 := by linear_combination hh
  rw [hz,Complex.zero_re] at hS
  exact (lt_irrefl 0) hS




theorem preferred_sine_re_pos_of_strip (z : ℂ) (hz : 0 < z.re) (hzπ : z.re < Real.pi) :
    0 < (Complex.sin z).re := by
  rw [Complex.sin_eq]
  simpa [← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh] using
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hz hzπ) (Real.cosh_pos z.im)

/-- The physical half-difference strip gives both actual slit-plane margins
needed by the explicit inverse, even on the compact left arc. -/
theorem preferred_strip_cosine_slits (z : ℂ) (hz : 0 < z.re) (hzπ : z.re < Real.pi) :
    1-(Complex.cos z)^2 ∈ Complex.slitPlane ∧
      preferredCosineRoot (Complex.cos z) ∈ Complex.slitPlane := by
  have hs := preferred_sine_re_pos_of_strip z hz hzπ
  have hsq : 1-(Complex.cos z)^2 = (Complex.sin z)^2 := by
    linear_combination -(Complex.sin_sq_add_cos_sq z)
  constructor
  · rw [hsq]
    by_cases hi : (Complex.sin z).im=0
    · left
      simp only [pow_two,Complex.mul_re,hi,mul_zero,sub_zero]
      positivity
    · right
      rw [pow_two,Complex.mul_im,
        show (Complex.sin z).re*(Complex.sin z).im+(Complex.sin z).im*(Complex.sin z).re =
          2*(Complex.sin z).re*(Complex.sin z).im by ring]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hi
  · have hroot : preferredCosineRoot (Complex.cos z)=Complex.exp (z*Complex.I) := by
      unfold preferredCosineRoot
      rw [hsq,preferred_sqrt_sq_of_re_pos _ hs,Complex.exp_mul_I]
      ring
    rw [hroot]
    right
    have hh : 0 < (Complex.exp (z*Complex.I)).im := by
      simpa [Complex.exp_im,Complex.mul_re,Complex.mul_im] using
        mul_pos (Real.exp_pos (-z.im)) (Real.sin_pos_of_pos_of_lt_pi hz hzπ)
    exact hh.ne'

theorem complexRightInverse_argument (S w φ : ℂ)
    (hdisp : Complex.cos w+Complex.cos φ=S) (hc : Complex.cos ((w+φ)/2) ≠ 0) :
    S/(2*Complex.cos ((w+φ)/2))=Complex.cos ((φ-w)/2) := by
  have hs := Complex.cos_add_cos φ w
  rw [add_comm φ w,add_comm (Complex.cos φ) (Complex.cos w),hdisp] at hs
  rw [hs]
  field_simp

theorem complexRightInverse_analyticAt_of_strip (S w φ : ℂ)
    (hdisp : Complex.cos w+Complex.cos φ=S) (hc : Complex.cos ((w+φ)/2) ≠ 0)
    (hl : 0 < ((φ-w)/2).re) (hu : ((φ-w)/2).re < Real.pi) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => complexRightInverse z.1 z.2) (S,w+φ) := by
  obtain ⟨hs,hr⟩ := preferred_strip_cosine_slits ((φ-w)/2) hl hu
  apply complexRightInverse_analyticAt _ _ hc
  · rwa [complexRightInverse_argument S w φ hdisp hc]
  · rwa [complexRightInverse_argument S w φ hdisp hc]

/-- Differentiating the actual dispersion shows Uq cannot vanish at any
upper physical point on this strip. No lower bound for Uq is assumed. -/
theorem complexRightInverse_deriv_ne_zero_of_strip (S w φ : ℂ)
    (hdisp : Complex.cos w+Complex.cos φ=S) (hc : Complex.cos ((w+φ)/2) ≠ 0)
    (hl : 0 < ((φ-w)/2).re) (hu : ((φ-w)/2).re < Real.pi)
    (hsin : Complex.sin φ ≠ 0) : deriv (complexRightInverse S) (w+φ) ≠ 0 := by
  have hraw := complexRightInverse_analyticAt_of_strip S w φ hdisp hc hl hu
  have hparam : AnalyticAt ℂ (fun v : ℂ => (S,v)) (w+φ) := analyticAt_const.prod analyticAt_id
  have hU : AnalyticAt ℂ (complexRightInverse S) (w+φ) :=
    AnalyticAt.comp (f := fun v : ℂ => (S,v))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw hparam
  have hv := complexRightInverse_inverse S w φ hdisp hc hl hu
  have hd := hU.differentiableAt.hasDerivAt.ccos.add
    (((hasDerivAt_id (w+φ)).sub hU.differentiableAt.hasDerivAt).ccos)
  have hne : ∀ᶠ v in 𝓝 (w+φ), Complex.cos (v/2) ≠ 0 :=
    (by fun_prop : ContinuousAt (fun v : ℂ => Complex.cos (v/2)) (w+φ)).eventually_ne hc
  have heq : (fun v => Complex.cos (complexRightInverse S v)+
      Complex.cos (v-complexRightInverse S v)) =ᶠ[𝓝 (w+φ)] (fun _ => S) := by
    filter_upwards [hne] with v hv
    exact complexRightInverse_dispersion S v hv
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const (w+φ) S)
  intro hz
  apply hsin
  simpa only [Pi.sub_apply,id_eq,hv,hz,mul_zero,zero_add,sub_zero,add_sub_cancel_left,
    mul_one,neg_neg,neg_zero] using congrArg Neg.neg he

/-- Pointwise analytic regularity and nonzero Uq on the entire physical
one-sided contour, including all branch/compact mixtures. -/
theorem preferred_global_one_sided_q_regular (s w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθlo : -Real.pi-δ ≤ w.re) (hθhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace s-Complex.cos w).im) :
    let q := preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s
    AnalyticAt ℂ (preferredMovingInverse s) q ∧ deriv (preferredMovingInverse s) q ≠ 0 := by
  let φ := preferredArccos (temperatureTrace s-Complex.cos w)
  let q := φ+w-preferredMovingBranch s
  have hdisp : Complex.cos w+Complex.cos φ=temperatureTrace s := by
    rw [show Complex.cos φ=temperatureTrace s-Complex.cos w from cos_preferredArccos _]
    ring
  obtain ⟨hl,hu⟩ := preferred_half_difference_strip (temperatureTrace s) w δ
    hδ hδπ hS hSδ hθlo hθhi hW
  have hc : Complex.cos ((w+φ)/2) ≠ 0 := by
    intro hz
    have hh := Complex.cos_add_cos w φ
    rw [hz,mul_zero,zero_mul,hdisp] at hh
    rw [hh,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hraw := complexRightInverse_analyticAt_of_strip (temperatureTrace s) w φ hdisp hc hl hu
  have hparam : AnalyticAt ℂ (fun v : ℂ => (temperatureTrace s,v)) (w+φ) :=
    analyticAt_const.prod analyticAt_id
  have hraw₁ : AnalyticAt ℂ (complexRightInverse (temperatureTrace s)) (w+φ) :=
    AnalyticAt.comp (f := fun v : ℂ => (temperatureTrace s,v))
      (g := fun z : ℂ × ℂ => complexRightInverse z.1 z.2) hraw hparam
  have hqa : q+preferredMovingBranch s=w+φ := by dsimp [q]; ring
  have hcomp : AnalyticAt ℂ (preferredMovingInverse s) q :=
    hraw₁.comp_of_eq (analyticAt_id.add analyticAt_const) hqa
  refine ⟨hcomp,?_⟩
  have hs := IsingBulk.Branch.lowerArccos_sheet_of_upper hW
  change Complex.cos φ= _ ∧ 0<φ.re ∧ φ.re<Real.pi ∧ φ.im<0 at hs
  have hsin : Complex.sin φ ≠ 0 := by
    have hp := preferred_sine_re_pos_of_strip φ hs.2.1 hs.2.2.1
    intro hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hder := hraw₁.differentiableAt.hasDerivAt.comp_of_eq q
    ((hasDerivAt_id q).add_const (preferredMovingBranch s)) hqa.symm
  have hd : deriv (preferredMovingInverse s) q = deriv (complexRightInverse (temperatureTrace s)) (w+φ) := by
    convert! hder.deriv using 1
    simp only [mul_one]
  rw [hd]
  exact complexRightInverse_deriv_ne_zero_of_strip _ _ _ hdisp hc hl hu hsin

/-- The forward regular coordinate has the actual derivative Uq^{-1};
this proves the one-body factor of the complete coordinate Jacobian (7.4). -/
theorem preferred_forward_coordinate_hasDerivAt (s w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθlo : -Real.pi-δ ≤ w.re) (hθhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace s-Complex.cos w).im) :
    let q := preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s
    HasDerivAt (fun v : ℂ => preferredArccos (temperatureTrace s-Complex.cos v)+v-preferredMovingBranch s)
      (deriv (preferredMovingInverse s) q)⁻¹ w := by
  let φ : ℂ → ℂ := fun v => preferredArccos (temperatureTrace s-Complex.cos v)
  let F : ℂ → ℂ := fun v => φ v+v-preferredMovingBranch s
  have hinner : AnalyticAt ℂ (fun v : ℂ => temperatureTrace s-Complex.cos v) w := by fun_prop
  have houter : AnalyticAt ℂ preferredArccos (temperatureTrace s-Complex.cos w) :=
    IsingBulk.Branch.lowerArccos_analytic_of_upper hW
  have hφ : AnalyticAt ℂ φ w := AnalyticAt.comp
    (f := fun v : ℂ => temperatureTrace s-Complex.cos v) (g := preferredArccos) houter hinner
  have hF : AnalyticAt ℂ F w := (hφ.add analyticAt_id).sub analyticAt_const
  obtain ⟨hU,hUq⟩ := preferred_global_one_sided_q_regular s w δ hδ hδπ hS hSδ hθlo hθhi hW
  have hcosne (v : ℂ) : Complex.cos ((v+φ v)/2) ≠ 0 := by
    intro hz
    have hh := Complex.cos_add_cos v (φ v)
    rw [hz,mul_zero,zero_mul] at hh
    have hc : Complex.cos (φ v)=temperatureTrace s-Complex.cos v := cos_preferredArccos _
    rw [hc] at hh
    have hzero : temperatureTrace s=0 := by linear_combination hh
    rw [hzero,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hhalf : ContinuousAt (fun v : ℂ => ((φ v-v)/2).re) w :=
    Complex.continuous_re.continuousAt.comp ((hφ.continuousAt.sub continuousAt_id).div_const 2)
  obtain ⟨hl,hu⟩ := preferred_half_difference_strip (temperatureTrace s) w δ
    hδ hδπ hS hSδ hθlo hθhi hW
  have hegerm : (fun v => preferredMovingInverse s (F v)) =ᶠ[𝓝 w] id := by
    filter_upwards [continuousAt_const.eventually_lt hhalf hl,
      hhalf.eventually_lt continuousAt_const hu] with v hlv huv
    exact preferredMovingInverse_inverse s v (hcosne v) hlv huv
  have hchain := hU.differentiableAt.hasDerivAt.comp w hF.differentiableAt.hasDerivAt
  have he := (hchain.congr_of_eventuallyEq hegerm.symm).unique (hasDerivAt_id w)
  have hd : deriv F w = (deriv (preferredMovingInverse s) (F w))⁻¹ := by
    apply mul_left_cancel₀ hUq
    rw [he,mul_inv_cancel₀ hUq]
  have hf := hF.differentiableAt.hasDerivAt
  rw [hd] at hf
  exact hf

/-- The primitive one-sided trace margins hold uniformly on the selected
physical outward ray for every fixed endpoint 0<delta<alpha. -/
theorem preferred_radial_one_sided_margins (d : PreferredBranchData) (δ : ℝ)
    (hδ : 0 < δ) (hδα : δ < d.alpha) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < (preferredRadialTrace d ε).re ∧ 0 < (preferredRadialTrace d ε).im ∧
        (preferredRadialTrace d ε).re < 2*Real.cos δ := by
  have hcont : ContinuousAt (fun ε : ℝ => (preferredRadialTrace d ε).re) 0 := by
    dsimp [preferredRadialTrace,IsingBulk.Branch.radialParameter]
    fun_prop (disch := simp [Complex.exp_ne_zero])
  have hzero : (preferredRadialTrace d 0).re=2*Real.cos d.alpha := by
    rw [preferredRadialTrace_zero]
    simp only [Complex.ofReal_re,d.angle_relation]
    ring
  have hc : 0 < (preferredRadialTrace d 0).re := by
    rw [hzero]
    have hh := Real.cos_pos_of_mem_Ioo
      (show d.alpha ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩)
    positivity
  have hcδ : (preferredRadialTrace d 0).re < 2*Real.cos δ := by
    rw [hzero]
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hδ.le
      (by linarith [d.alpha_lt,Real.pi_pos]) hδα
    linarith
  obtain ⟨r,hr,hrange⟩ := Metric.eventually_nhds_iff.mp
    ((continuousAt_const.eventually_lt hcont hc).and (hcont.eventually_lt continuousAt_const hcδ))
  refine ⟨r,hr,?_⟩
  intro ε hε hεr
  have hh := hrange (y := ε) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using hεr)
  refine ⟨hh.1,?_,hh.2⟩
  have he : 1+ε ≠ 0 := by positivity
  have hs := (IsingBulk.Branch.radial_trace_components d.alpha ε he).2
  change 0 < (IsingBulk.Branch.radialParameter d.alpha ε+
    (IsingBulk.Branch.radialParameter d.alpha ε)⁻¹).im
  rw [hs]
  have hfrac : ε^2/(1+ε) < 2*ε :=
    (div_lt_iff₀ (by positivity : 0 < 1+ε)).mpr (by nlinarith [sq_nonneg ε])
  apply mul_pos (by linarith)
  exact Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt,Real.pi_pos])

/-- The moving center is analytic in the physical parameter on its upper
trace sheet; this is a statement about the explicit source branch. -/
theorem preferredMovingBranch_analyticAt_upper (s : ℂ)
    (hSi : 0 < (temperatureTrace s).im) : AnalyticAt ℂ preferredMovingBranch s := by
  have hs0 : s ≠ 0 := by intro hz; simp [hz,temperatureTrace] at hSi
  have hS : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs0)
  have hW : 0 < (temperatureTrace s-1).im := by simpa using hSi
  have ho : AnalyticAt ℂ preferredArccos (temperatureTrace s-1) :=
    IsingBulk.Branch.lowerArccos_analytic_of_upper hW
  exact (AnalyticAt.comp (f := fun t : ℂ => temperatureTrace t-1)
    (g := preferredArccos) ho (hS.sub analyticAt_const)).neg

/-- Joint physical-s and q analyticity at every actual point of the entire
one-sided contour. The remaining uniform-domain obligation is stronger and
is not inferred from this pointwise result. -/
theorem preferred_global_one_sided_joint_analytic (s w : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hS : 0 < (temperatureTrace s).re) (hSi : 0 < (temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re < 2*Real.cos δ)
    (hθlo : -Real.pi-δ ≤ w.re) (hθhi : w.re ≤ δ)
    (hW : 0 < (temperatureTrace s-Complex.cos w).im) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredArccos (temperatureTrace s-Complex.cos w)+w-preferredMovingBranch s) := by
  let φ := preferredArccos (temperatureTrace s-Complex.cos w)
  let q := φ+w-preferredMovingBranch s
  have hdisp : Complex.cos w+Complex.cos φ=temperatureTrace s := by
    rw [show Complex.cos φ=temperatureTrace s-Complex.cos w from cos_preferredArccos _]
    ring
  obtain ⟨hl,hu⟩ := preferred_half_difference_strip (temperatureTrace s) w δ
    hδ hδπ hS hSδ hθlo hθhi hW
  have hc : Complex.cos ((w+φ)/2) ≠ 0 := by
    intro hz
    have hh := Complex.cos_add_cos w φ
    rw [hz,mul_zero,zero_mul,hdisp] at hh
    rw [hh,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hraw := complexRightInverse_analyticAt_of_strip (temperatureTrace s) w φ hdisp hc hl hu
  have hs0 : s ≠ 0 := by intro hz; simp [hz,temperatureTrace] at hSi
  have hSa : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs0)
  have hBa := preferredMovingBranch_analyticAt_upper s hSi
  have hSf : AnalyticAt ℂ (fun z : ℂ × ℂ => temperatureTrace z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := temperatureTrace) hSa analyticAt_fst
  have hBf : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch) hBa analyticAt_fst
  have hmap : AnalyticAt ℂ
      (fun z : ℂ × ℂ => (temperatureTrace z.1,z.2+preferredMovingBranch z.1)) (s,q) :=
    hSf.prod (analyticAt_snd.add hBf)
  have heq : (temperatureTrace s,q+preferredMovingBranch s)=(temperatureTrace s,w+φ) := by
    congr 1
    dsimp [q]
    ring
  exact hraw.comp_of_eq hmap heq


end
end IsingBulk.Preferred22
