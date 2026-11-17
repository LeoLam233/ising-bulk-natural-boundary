import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorScalar
import IsingBulk.AnisoF002.C03.RegularFiniteRootStability

/-!
# Common anchored analytic disks for the complete regular density

The entire physical product kernel is retained in the analytic amplitude.
One radius divided by N protects its full product and the named inverse
slope. All other factors retain the actual one-sided Gaussian bound.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric
open IsingBulk.AnisoF002.RegularTail.C03

def regularRootProduct {N : ℕ} (p : RegularJointSpace N) : ℂ :=
  ∏ i, regularInverseRoot (p.1, p.2 i)

def regularProductKernel {N : ℕ} (σ : ℂ) (p : RegularJointSpace N) : ℂ :=
  (1 + σ * regularRootProduct p) / (1 - σ * regularRootProduct p)

def anchoredRegularDensity {N : ℕ} (σ : ℂ) (p : RegularJointSpace N) : ℂ :=
  isotropicParticleNormalization N * regularProductKernel σ p * completeRegularNumerator N p

theorem regularRootProduct_analyticAt {N : ℕ} (p : RegularJointSpace N)
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (p.1, p.2 i)) :
    AnalyticAt ℂ regularRootProduct p := by
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (regularInverseRoot_analyticAt _ (hU i)).comp
    (f := fun q : RegularJointSpace N => (q.1, q.2 i))
    (analyticAt_fst.prod (coordinate_analyticAt p i))

theorem regularProductKernel_control {N : ℕ} (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (p : RegularJointSpace N) (q : ℝ) (_hq : 0 ≤ q) (hq1 : q < 1)
    (hp : ‖regularRootProduct p‖ ≤ (1 + q) / 2)
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (p.1, p.2 i)) :
    AnalyticAt ℂ (regularProductKernel σ) p ∧
      ‖regularProductKernel σ p‖ ≤ 4 / (1 - q) := by
  have hqgap : 0 < (1 - q) / 2 := by linarith
  have hz : ‖σ * regularRootProduct p‖ ≤ (1 + q) / 2 := by
    rw [norm_mul]
    exact (mul_le_mul hσ hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hden : (1 - q) / 2 ≤ ‖1 - σ * regularRootProduct p‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (σ * regularRootProduct p)
    rw [norm_one] at hh
    linarith
  have hne : 1 - σ * regularRootProduct p ≠ 0 := norm_pos_iff.mp (hqgap.trans_le hden)
  have hR := regularRootProduct_analyticAt p hU
  refine ⟨(analyticAt_const.add (analyticAt_const.mul hR)).div
    (analyticAt_const.sub (analyticAt_const.mul hR)) hne, ?_⟩
  have hnum : ‖1 + σ * regularRootProduct p‖ ≤ 2 := by
    have hh := norm_add_le (1 : ℂ) (σ * regularRootProduct p)
    rw [norm_one] at hh
    linarith
  rw [regularProductKernel, norm_div]
  exact (div_le_div₀ (by norm_num) hnum hqgap hden).trans_eq (by field_simp; ring)

/-- All constants precede population, anchor, physical sign, and every
derivative order. The center hypotheses are the actual physical bounds
discharged by the compact-left cutoff and the original upper sheet. -/
theorem exists_uniform_anchored_regular_disks (S c₀ q₀ : ℝ)
    (hS : 0 < S ∧ S < 2) (hc₀ : 0 < c₀) (hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1) :
    ∃ r ρ κ A L : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < κ ∧ 0 < A ∧ 0 < L ∧
      ∀ N : ℕ, 0 < N → ∀ a : Fin N, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ p : RegularJointSpace N, p ∈ oneSidedProductDomain S r N →
      (∀ i, ‖regularInverseRoot (p.1, p.2 i)‖ ≤ 1) →
      ‖regularInverseRoot (p.1, p.2 a)‖ ≤ q₀ →
      c₀ ≤ ‖jointCoordinateDerivative explicitRightInverse (p.1, p.2 a)‖ →
      ∀ z ∈ ball p (ρ / (N : ℝ)),
        AnalyticAt ℂ (anchoredRegularField a) z ∧
        (∀ i, AnalyticAt ℂ (fun y => anchoredCutoffCoefficient a y i) z) ∧
        AnalyticAt ℂ (anchoredRegularDensity σ) z ∧
        ‖anchoredRegularField a z‖ ≤ L * N ∧
        (∀ i, ‖anchoredCutoffCoefficient a z i‖ ≤ L * N) ∧
        ‖anchoredRegularDensity σ z‖ ≤
          ‖isotropicParticleNormalization N‖ * (4 / (1 - q₀)) * A ^ N *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨rS, C, hrS, hC1, hscalar⟩ := exists_oneSided_scalar_transport_control S hS
  obtain ⟨rG, κ, A, M, hrG, hκ, hA, _, hgauss⟩ :=
    exists_actual_oneSided_retainedNumerator_analytic_gaussian S hS
  have hC : 0 < C := zero_lt_one.trans_le hC1
  let r := min (rS / 2) (rG / 2)
  have hr : 0 < r := lt_min (half_pos hrS) (half_pos hrG)
  have hrrS : r ≤ rS / 2 := min_le_left _ _
  have hrrG : r ≤ rG / 2 := min_le_right _ _
  let ρ := min r (min (c₀ / (2 * C)) (min (1 / C) ((1 - q₀) / (2 * C * Real.exp 1))))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r := min_le_left _ _
  have hρc : ρ ≤ c₀ / (2 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have hρC : ρ ≤ 1 / C := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρq : ρ ≤ (1 - q₀) / (2 * C * Real.exp 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCρc : C * ρ ≤ c₀ / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp hρc
    nlinarith
  have hCρ1 : C * ρ ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp hρC
    nlinarith
  have hCρq : C * ρ * Real.exp 1 ≤ (1 - q₀) / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * C * Real.exp 1 by positivity)).mp hρq
    nlinarith
  let L := 1 + 2 * C / c₀ + C + 2 * C ^ 2 / c₀
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨r, ρ, κ, A, L, hr, hρ, hκ, hA, hL, ?_⟩
  intro N hN a σ hσ p hp hrp hanchor hslope z hz
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrad : ρ / (N : ℝ) ≤ ρ := div_le_self hρ.le hn1
  have hzp : dist z p < ρ / (N : ℝ) := hz
  have hzpS : dist z p < rS / 2 := hzp.trans_le (hrad.trans (hρr.trans hrrS))
  have hzpG : dist z p < rG / 2 := hzp.trans_le (hrad.trans (hρr.trans hrrG))
  have hpS := oneSidedProductDomain_mono S hrrS N hp
  have hpG := oneSidedProductDomain_mono S hrrG N hp
  have hzG : z ∈ oneSidedProductDomain S rG N :=
    oneSidedProductDomain_half_ball_subset S rG N p hpG hzpG
  have hscenter (i : Fin N) : (p.1, p.2 i) ∈ thickening (rS / 2) (oneSidedParameterArc S) :=
    oneSidedSingle_of_thickening hpS.1 (hpS.2 i)
  have hcoord (i : Fin N) : ‖(z.1, z.2 i) - (p.1, p.2 i)‖ ≤ dist z p := by
    rw [← dist_eq_norm, Prod.dist_eq, Prod.dist_eq]
    exact max_le (le_max_left _ _) ((dist_le_pi_dist z.2 p.2 i).trans (le_max_right _ _))
  have hzscalar (i : Fin N) : (z.1, z.2 i) ∈ cthickening rS (oneSidedParameterArc S) :=
    oneSidedScalar_half_ball_subset (hscenter i)
      (show dist (z.1, z.2 i) (p.1, p.2 i) < rS / 2 by
        rw [dist_eq_norm]; exact (hcoord i).trans_lt hzpS)
  have hU (i : Fin N) := (hscalar _ (hzscalar i)).1
  have hRdiff (i : Fin N) :
      ‖regularInverseRoot (z.1, z.2 i) - regularInverseRoot (p.1, p.2 i)‖ ≤ C * ρ / N := by
    have hh := oneSidedScalar_lipschitz hrS regularInverseRoot
      (fun y hy => (hscalar y hy).2.1.differentiableAt)
      (fun y hy => (hscalar y hy).2.2.2.2.1) _ (hscenter i) _
      (show dist (z.1, z.2 i) (p.1, p.2 i) < rS / 2 by
        rw [dist_eq_norm]; exact (hcoord i).trans_lt hzpS)
    exact hh.trans ((mul_le_mul_of_nonneg_left ((hcoord i).trans hzp.le) hC.le).trans_eq (by ring))
  have hVdiff : ‖jointCoordinateDerivative explicitRightInverse (z.1, z.2 a) -
      jointCoordinateDerivative explicitRightInverse (p.1, p.2 a)‖ ≤ C * ρ / N := by
    have hh := oneSidedScalar_lipschitz hrS (jointCoordinateDerivative explicitRightInverse)
      (fun y hy => (hscalar y hy).2.2.1.differentiableAt)
      (fun y hy => (hscalar y hy).2.2.2.2.2) _ (hscenter a) _
      (show dist (z.1, z.2 a) (p.1, p.2 a) < rS / 2 by
        rw [dist_eq_norm]; exact (hcoord a).trans_lt hzpS)
    exact hh.trans ((mul_le_mul_of_nonneg_left ((hcoord a).trans hzp.le) hC.le).trans_eq (by ring))
  have hsmall : C * ρ / (N : ℝ) ≤ c₀ / 2 :=
    (div_le_self (by positivity) hn1).trans hCρc
  have hslopez : c₀ / 2 ≤ ‖jointCoordinateDerivative explicitRightInverse (z.1, z.2 a)‖ := by
    have ht := norm_le_norm_sub_add
      (jointCoordinateDerivative explicitRightInverse (p.1, p.2 a))
      (jointCoordinateDerivative explicitRightInverse (z.1, z.2 a))
    rw [norm_sub_rev] at ht
    linarith
  have hvne : jointCoordinateDerivative explicitRightInverse (z.1, z.2 a) ≠ 0 :=
    norm_pos_iff.mp ((half_pos hc₀).trans_le hslopez)
  have hSz (i : Fin N) : ‖jointParameterDerivative explicitRightInverse (z.1, z.2 i)‖ ≤ C :=
    (jointParameterDerivative_norm_le _ _ (hU i).differentiableAt).trans (hscalar _ (hzscalar i)).2.2.2.1
  have hVz (i : Fin N) : ‖jointCoordinateDerivative explicitRightInverse (z.1, z.2 i)‖ ≤ C :=
    (jointCoordinateDerivative_norm_le _ _ (hU i).differentiableAt).trans (hscalar _ (hzscalar i)).2.2.2.1
  have hprod := finite_prod_perturbation
    (fun i => regularInverseRoot (p.1, p.2 i)) (fun i => regularInverseRoot (z.1, z.2 i))
    (show 0 ≤ C * ρ / (N : ℝ) by positivity) hrp hRdiff
  have hNh : (N : ℝ) * (C * ρ / (N : ℝ)) ≤ 1 := by
    rw [mul_div_cancel₀ _ hn.ne']
    exact hCρ1
  have hpold : ‖regularRootProduct p‖ ≤ q₀ :=
    (product_norm_le_named_factor _ hrp a).trans hanchor
  have hpnew : ‖regularRootProduct z‖ ≤ (1 + q₀) / 2 := by
    have hexp := one_add_pow_le_exp_one (show 0 ≤ C * ρ / (N : ℝ) by positivity) N hNh
    have hdiff : ‖regularRootProduct z - regularRootProduct p‖ ≤ (1 - q₀) / 2 := by
      exact hprod.trans ((mul_le_mul_of_nonneg_left hexp (by positivity)).trans
        (by convert hCρq using 1; field_simp))
    have ht := norm_le_norm_sub_add (regularRootProduct z) (regularRootProduct p)
    linarith
  obtain ⟨hkernel, hkernelBound⟩ := regularProductKernel_control σ hσ z q₀ hq₀ hq₀1 hpnew hU
  obtain ⟨hnum, hnumb⟩ := hgauss N ∅ (Finset.empty_subset _) z hzG
  rw [retainedRegularNumerator_empty] at hnum hnumb
  simp only [Finset.card_empty, pow_zero, mul_one] at hnumb
  refine ⟨anchoredRegularField_analyticAt a z hU hvne,
    fun i => anchoredCutoffCoefficient_analyticAt a z hU hvne i,
    (analyticAt_const.mul hkernel).mul hnum, ?_, ?_, ?_⟩
  · have hh := anchoredRegularField_norm_bound a z C (c₀ / 2) hC.le (half_pos hc₀) hSz hslopez
    apply hh.trans
    have he : (N : ℝ) * C / (c₀ / 2) = (2 * C / c₀) * N := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hn.le
    dsimp [L]
    have hc2 : 0 ≤ 2 * C ^ 2 / c₀ := by positivity
    linarith only [hC, hc2]
  · intro i
    have hh := anchoredCutoffCoefficient_norm_bound a z C (c₀ / 2) hC.le (half_pos hc₀) hSz hVz hslopez i
    apply hh.trans
    have he : C * (1 + (N : ℝ) * C / (c₀ / 2)) = C + (2 * C ^ 2 / c₀) * N := by ring
    rw [he]
    calc
      _ ≤ C * N + (2 * C ^ 2 / c₀) * N :=
        add_le_add (le_mul_of_one_le_right hC.le hn1) le_rfl
      _ = (C + 2 * C ^ 2 / c₀) * N := by ring
      _ ≤ L * N := by
        apply mul_le_mul_of_nonneg_right _ hn.le
        dsimp [L]
        have hc1 : 0 ≤ 2 * C / c₀ := by positivity
        linarith only [hc1]
  · rw [anchoredRegularDensity, norm_mul, norm_mul]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hkernelBound (norm_nonneg _)) hnumb
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

end IsingBulk.AnisoF002.Isotropic
