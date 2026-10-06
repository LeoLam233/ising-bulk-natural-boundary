import IsingBulk.Analysis.JetsChart
import IsingBulk.Analysis.LieTransport

/-! The selected-pair field on the actual original angular chart. Parameters
v and theta specify the fixed circle and fixed lower branch center. -/
namespace IsingBulk.Jets
noncomputable section
open scoped BigOperators
open IsingBulk.Lie

def actualField {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) : Fin (n+1) → ℂ :=
  selectedField (fun i => chartA s v θ (x i)) (fun i => chartB s v θ (x i)) p q

def actualY {n : ℕ} (v θ : ℝ) (_s : ℂ) (x : AngularSpace n) : ℂ :=
  Complex.exp (∑ i, ((v:ℂ)+((x i:ℂ)-(θ:ℂ))*Complex.I))

def actualZ {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  Complex.exp (-Complex.I * ∑ i, chartPhase s v θ (x i))

theorem actualY_eq_product {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) :
    actualY v θ s x = ∏ i, angularY v θ (x i) := by
  simp only [actualY, Complex.exp_sum, angularY]

theorem actualZ_eq_product {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) :
    actualZ v θ s x = ∏ i, Complex.exp (-Complex.I * chartPhase s v θ (x i)) := by
  simp only [actualZ, Finset.mul_sum, Complex.exp_sum]

theorem actualField_sum {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n)
    (hd : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0) :
    ∑ i, actualField v θ p q s x i = 0 := selectedField_sum _ _ p q hd

theorem phase_sum_parameter {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    HasDerivAt (fun t => ∑ i, chartPhase t v θ (x i))
      (∑ i, chartB s v θ (x i)*chartA s v θ (x i)) s := by
  apply HasDerivAt.fun_sum
  intro i _
  rw [chartB_mul_chartA s v θ (x i) (hg i)]
  exact chartPhase_parameter s v θ (x i) hs (hr i) (hi i)

theorem actualField_weighted_sum {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    ∑ i, chartB s v θ (x i)*actualField v θ p q s x i =
      deriv (fun t => ∑ i, chartPhase t v θ (x i)) s := by
  rw [(phase_sum_parameter v θ s x hs hr hi hg).deriv]
  exact selectedField_weighted_sum _ _ p q

theorem coordinate_hasFDerivAt {n : ℕ} (f : ℝ → ℂ) (d : ℂ)
    (x : AngularSpace n) (i : Fin (n+1)) (hf : HasDerivAt f d (x i)) :
    HasFDerivAt (fun y : AngularSpace n => f (y i))
      ((ContinuousLinearMap.proj (R := ℝ) i).smulRight d) x := by
  convert! hf.hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) i x) using 1

theorem phase_sum_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    HasFDerivAt (fun y : AngularSpace n => ∑ i, chartPhase s v θ (y i))
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) i).smulRight (chartB s v θ (x i))) x := by
  exact HasFDerivAt.fun_sum fun i _ => coordinate_hasFDerivAt _ _ x i
    (chartPhase_real_angular s v θ (x i) (hr i) (hi i))

theorem actualY_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) :
    HasFDerivAt (actualY v θ s)
      (actualY v θ s x •
        (∑ i : Fin (n+1), (ContinuousLinearMap.proj (R := ℝ) i).smulRight Complex.I)) x := by
  have h : HasFDerivAt
      (fun y : AngularSpace n => ∑ i, ((v:ℂ)+((y i:ℂ)-(θ:ℂ))*Complex.I))
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) i).smulRight Complex.I) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    apply coordinate_hasFDerivAt (fun t : ℝ => (v:ℂ)+((t:ℂ)-(θ:ℂ))*Complex.I)
    convert! ((((hasDerivAt_id (x i:ℂ)).comp_ofReal).sub_const (θ:ℂ)).mul_const Complex.I).const_add (v:ℂ) using 1
    simp
  exact h.cexp

theorem actualY_frozen {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n)
    (hd : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0) :
    transport (actualField v θ p q) (actualY v θ) s x = 0 := by
  unfold transport
  rw [(actualY_spatial v θ s x).fderiv]
  simp only [actualY, deriv_const, ContinuousLinearMap.smulRight_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, actualField_sum v θ p q s x hd,
    zero_mul, sub_zero]

theorem actualZ_parameter {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hs : s ≠ 0) (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    HasDerivAt (fun t => actualZ v θ t x)
      (actualZ v θ s x * (-Complex.I * ∑ i, chartB s v θ (x i)*chartA s v θ (x i))) s :=
  ((phase_sum_parameter v θ s x hs hr hi hg).const_mul (-Complex.I)).cexp

theorem actualZ_spatial {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im) :
    HasFDerivAt (actualZ v θ s)
      (actualZ v θ s x • (-Complex.I •
        ∑ i, (ContinuousLinearMap.proj (R := ℝ) i).smulRight (chartB s v θ (x i)))) x := by
  exact ((phase_sum_spatial v θ s x hr hi).const_smul (-Complex.I)).cexp

theorem actualZ_frozen {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    transport (actualField v θ p q) (actualZ v θ) s x = 0 := by
  unfold transport
  rw [(actualZ_parameter v θ s x hs hr hi hg).deriv,
    (actualZ_spatial v θ s x hr hi).fderiv]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    smul_eq_mul]
  have hsum : (∑ i, actualField v θ p q s x i *
      (actualZ v θ s x * (-Complex.I * chartB s v θ (x i)))) =
      actualZ v θ s x * (-Complex.I * ∑ i, chartB s v θ (x i)*actualField v θ p q s x i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, show (∑ i, chartB s v θ (x i)*actualField v θ p q s x i) =
    ∑ i, chartB s v θ (x i)*chartA s v θ (x i) from selectedField_weighted_sum _ _ p q]
  ring

/-- Source Y and Z supply the hypotheses of the already proved local
simple-kernel transport rule; freezing is proved here from the actual chart. -/
theorem actual_simpleKernel_frozen {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0)
    (hd : chartB s v θ (x p)-chartB s v θ (x q) ≠ 0)
    (hY : 1-actualY v θ s x ≠ 0) (hZ : 1-actualZ v θ s x ≠ 0) :
    transport (actualField v θ p q) (simpleKernel (actualY v θ) (actualZ v θ)) s x = 0 := by
  exact simpleKernel_frozen _ _ _ s x (differentiableAt_const _)
    (actualZ_parameter v θ s x hs hr hi hg).differentiableAt
    (actualY_spatial v θ s x).differentiableAt
    (actualZ_spatial v θ s x hr hi).differentiableAt hY hZ
    (actualY_frozen v θ p q s x hd) (actualZ_frozen v θ p q s x hs hr hi hg)

/-- This is the actual time derivative minus chart pushforward, rather than
an independent algebraic residual supplied by a caller. -/
def actualResidual {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (i : Fin (n+1)) : ℂ :=
  deriv (fun t => chartPhase t v θ (x i)) s -
    chartB s v θ (x i)*actualField v θ p q s x i

theorem actualResidual_eq {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    actualResidual v θ p q s x =
      residualField (fun i => chartA s v θ (x i)) (fun i => chartB s v θ (x i)) p q := by
  funext i
  rw [actualResidual, (chartPhase_parameter s v θ (x i) hs (hr i) (hi i)).deriv,
    ← chartB_mul_chartA s v θ (x i) (hg i)]
  rfl

theorem actualResidual_two_entries {n : ℕ} (v θ : ℝ) (p q : Fin (n+1)) (hpq : p ≠ q)
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, angularG v θ (x i) ≠ 0) :
    actualResidual v θ p q s x = fun i =>
      (if i = p then -(∑ k, chartA s v θ (x k))*chartB s v θ (x p)*
        chartB s v θ (x q)/(chartB s v θ (x p)-chartB s v θ (x q)) else 0) +
      (if i = q then (∑ k, chartA s v θ (x k))*chartB s v θ (x p)*
        chartB s v θ (x q)/(chartB s v θ (x p)-chartB s v θ (x q)) else 0) := by
  rw [actualResidual_eq v θ p q s x hs hr hi hg]
  exact residualField_two_entries _ _ p q hpq

end
end IsingBulk.Jets

