import IsingBulk.AnisoF002.C03.IsotropicCovarianceDisks
import IsingBulk.AnisoF002.C03.IsotropicRightHomotopy

/-!
# Complete joint field jets on actual right images

The numerical variance hypothesis of the protected-disk estimate is
discharged by the actual balanced contour. The resulting disks and all
joint derivatives permit every proper partial diagonal. Their radius
is quadratic in a selected angular gap; this already suffices away from
total equality. The sharper branch-shell radius is not asserted here.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem selected_pair_le_realPairEnergy {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (i j : ι) : (θ i - θ j) ^ 2 / 2 ≤ realPairEnergy θ := by
  classical
  have h₁ : (θ i - θ j) ^ 2 ≤ ∑ l, (θ i - θ l) ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (θ i - θ l)) (Finset.mem_univ j)
  have h₂ : (∑ l, (θ i - θ l) ^ 2) ≤ ∑ k, ∑ l, (θ k - θ l) ^ 2 :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (θ k - θ l)))
      (Finset.mem_univ i)
  unfold realPairEnergy
  linarith

/-- All joint analytic jets of the actual covariance field, with an
explicit protected radius and with no supplied variance or analyticity
assumption. Only the genuine total-equality singularity is excluded. -/
theorem exists_actual_covariance_protected_jets (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ r C : ℝ, 0 < δ ∧ 0 < r ∧ 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j →
        let q := actualHomotopyRegularTuple s η τ ξ θ
        let d := (θ i - θ j) ^ 2 / 4
        (∀ p ∈ ball q (covarianceProtectedRadius r C d N),
          AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
          d / 2 ≤ ‖pairVariance (fun k => explicitRightInverse (p.1, p.2 k))‖ ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ 2 * C ^ 2 * (N : ℝ) ^ 2 / d) ∧
        ∀ k : ℕ,
          ‖iteratedFDeriv ℂ k (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q‖ ≤
            protectedJetConstant k (covarianceProtectedRadius r C d N) *
              (2 * C ^ 2 * (N : ℝ) ^ 2 / d) := by
  obtain ⟨r, C, hr, hC, hdisks⟩ := exists_right_covariance_protected_disks S hS
  obtain ⟨δ₁, hδ₁, himage⟩ := exists_actual_right_homotopy_domain S (r / 2) hS (half_pos hr)
  obtain ⟨δ₂, hδ₂, hcoercive⟩ := exists_actual_variance_coercivity η
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ, r, C, hδ, hr, hC, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij
  have hθ1 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ₁) δ₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  obtain ⟨hq, hU⟩ := himage N hN s hs (hsnear.trans_le hd1) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hd1⟩ hξ θ hθ1
  have he : (fun k => explicitRightInverse (s, (actualHomotopyRegularTuple s η τ ξ θ).2 k)) =
      actualHomotopyAngle η τ ξ θ := funext hU
  have hvar := hcoercive N hN τ ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ
  have henergy := selected_pair_le_realPairEnergy θ i j
  have hd : 0 < (θ i - θ j) ^ 2 / 4 := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hij)) (by norm_num)
  apply hdisks N hN _ hq _ hd
  change (θ i - θ j) ^ 2 / 4 ≤
    (pairVariance (fun k => explicitRightInverse (s, (actualHomotopyRegularTuple s η τ ξ θ).2 k))).re
  rw [he]
  linarith

theorem protectedJetConstant_div (k : ℕ) (r a : ℝ) (ha : a ≠ 0) :
    protectedJetConstant k (r / a) = a ^ k * protectedJetConstant k r := by
  induction k generalizing r with
  | zero => simp [protectedJetConstant]
  | succ k ih =>
    simp only [protectedJetConstant]
    rw [show r / a / 2 = (r / 2) / a by ring, ih]
    rw [pow_succ]
    field_simp

end IsingBulk.AnisoF002.Isotropic
