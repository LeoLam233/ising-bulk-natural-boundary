import IsingBulk.AnisoF002.C03.IsotropicSharpCovarianceDisks

/-!
# The covariance geometric domain precedes all shell constants

The protected inverse/secant domain is selected before A, K and Δ's
upper envelope. Only the actual small ball radius and field bound depend
on these constants. This exposes the quantifier order of the checked
variance-perturbation argument without changing its formulas.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

theorem exists_right_sharp_covariance_buffer (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ A K D₀ : ℝ, 0 < A → 0 < K → 0 < D₀ →
      ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ (N : ℕ), 0 < N → ∀ q ∈ rightProductDomain S (R / 2) N,
      ∀ r t Δ : ℝ, 0 < r → 0 < t → 0 < Δ → t * Δ = r → Δ ≤ t → Δ ≤ D₀ →
        (∀ i j, ‖q.2 i - q.2 j‖ ≤ A * Δ) →
        (∀ i, ‖deriv (fun z => explicitRightInverse (q.1, z)) (q.2 i)‖ ≤ K * t) →
        (∀ i j, ‖explicitRightInverse (q.1, q.2 i) - explicitRightInverse (q.1, q.2 j)‖ ≤ 4 * r) →
        r ^ 2 / 4 ≤ (pairVariance (fun i => explicitRightInverse (q.1, q.2 i))).re →
        (∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2),
          AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
          r ^ 2 / 8 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ ∧
          ‖rightCovarianceField p.1 p.2‖ ≤ B * (N : ℝ) ^ 2 / Δ) ∧
        ∀ k : ℕ,
          ‖iteratedFDeriv ℂ k (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q‖ ≤
            protectedJetConstant k (c * Δ / (N : ℝ) ^ 2) * (B * (N : ℝ) ^ 2 / Δ) := by
  obtain ⟨R, L, hR, hL1, hU, hfirst, hsecond, hsecondNe, hUS, hsecondInv, hLip⟩ :=
    exists_right_sharp_covariance_primitives S hS
  refine ⟨R, hR, ?_⟩
  intro A K D₀ hA hK hD₀
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let M := 2 * K + 2 * L + L * A
  let H := (A + 2) * (K + L * (A + 1)) ^ 2 * L
  let c := min 1 (min (R / (2 * D₀)) (1 / (64 * M)))
  let B := 8 * L * H
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcR : c ≤ R / (2 * D₀) := (min_le_right _ _).trans (min_le_left _ _)
  have hcM : c ≤ 1 / (64 * M) := (min_le_right _ _).trans (min_le_right _ _)
  have hcMsmall : M * c ≤ 1 / 64 := by
    have hh := (le_div_iff₀ (show 0 < 64 * M by positivity)).mp hcM
    nlinarith only [hh]
  have hcD : c * D₀ ≤ R / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D₀ by positivity)).mp hcR
    nlinarith only [hh]
  refine ⟨c, B, hc, by dsimp [B]; positivity, ?_⟩
  intro N hN q hq r t Δ hr ht hΔ htΔ hΔt hΔD hcoord hUv hdiff hvariance
  let ρ := c * Δ / (N : ℝ) ^ 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρc : ρ ≤ c * Δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    exact le_mul_of_one_le_right (mul_nonneg hc.le hΔ.le) hN2
  have hρΔ : ρ ≤ Δ := hρc.trans (by nlinarith only [hc1, hΔ])
  have hρt : ρ ≤ t := hρΔ.trans hΔt
  have hρR : ρ ≤ R / 2 := hρc.trans
    ((mul_le_mul_of_nonneg_left hΔD hc.le).trans hcD)
  have hqR : q ∈ rightProductDomain S R N :=
    rightProductDomain_mono S (by linarith only [hR] : R / 2 ≤ R) N hq
  have hball : ball q ρ ⊆ rightProductDomain S R N :=
    (ball_subset_ball hρR).trans (rightProductDomain_half_ball_subset S R N q hq)
  have hqpair (i j : Fin N) : (q.1, q.2 i, q.2 j) ∈ thickening R (rightPairParameterSegment S) :=
    rightPair_of_thickening hqR.1 (hqR.2 i) (hqR.2 j)
  have hall : ∀ p ∈ ball q ρ,
      AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) p ∧
      r ^ 2 / 8 ≤ ‖pairVariance (fun i => explicitRightInverse (p.1, p.2 i))‖ ∧
      ‖rightCovarianceField p.1 p.2‖ ≤ B * (N : ℝ) ^ 2 / Δ := by
    intro p hp
    have hpR := hball hp
    have hpn : ‖p - q‖ ≤ ρ := by
      exact (show ‖p - q‖ < ρ by simpa only [mem_ball, dist_eq_norm] using hp).le
    have hparts : ‖p.1 - q.1‖ ≤ ρ ∧ ‖p.2 - q.2‖ ≤ ρ := by
      simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_le_iff] using hpn
    have hpcoord (i : Fin N) : ‖p.2 i - q.2 i‖ ≤ ρ :=
      (norm_le_pi_norm (p.2 - q.2) i).trans hparts.2
    have hpsingle (i : Fin N) : (p.1, p.2 i) ∈ cthickening R (rightParameterSegment S) :=
      thickening_subset_cthickening R _ (rightSingle_of_thickening hpR.1 (hpR.2 i))
    have hppair (i j : Fin N) : (p.1, p.2 i, p.2 j) ∈ thickening R (rightPairParameterSegment S) :=
      rightPair_of_thickening hpR.1 (hpR.2 i) (hpR.2 j)
    have hmove (i j : Fin N) :
        ‖(explicitRightInverse (p.1, p.2 i) - explicitRightInverse (p.1, p.2 j)) -
          (explicitRightInverse (q.1, q.2 i) - explicitRightInverse (q.1, q.2 j))‖ ≤
            (M * c) * r / (N : ℝ) ^ 2 := by
      have hh := inverse_difference_sharp_perturbation explicitRightInverse
        (thickening R (rightPairParameterSegment S)) L K A t Δ ρ
        hL.le hA.le hΔ.le hρ.le hΔt hρt hLip
        q.1 p.1 (q.2 i) (p.2 i) (q.2 j) (p.2 j)
        (hqpair i i) (hqpair j j) (hqpair i j)
        (rightPair_of_thickening hpR.1 (hqR.2 i) (hqR.2 j))
        (rightPair_of_thickening hpR.1 (hpR.2 i) (hqR.2 i))
        (rightPair_of_thickening hpR.1 (hpR.2 j) (hqR.2 j))
        hparts.1 (hpcoord i) (hpcoord j) (hcoord i j) (hUv i) (hUv j)
      apply hh.trans_eq
      dsimp [ρ, M]
      rw [← htΔ]
      ring
    have hstable := pairVariance_shell_stability hN
      (fun i => explicitRightInverse (q.1, q.2 i)) (fun i => explicitRightInverse (p.1, p.2 i))
      r (M * c) hr (mul_nonneg hM.le hc.le) hcMsmall hdiff hmove hvariance
    have hne : pairVariance (fun i => explicitRightInverse (p.1, p.2 i)) ≠ 0 :=
      norm_pos_iff.mp ((by positivity : 0 < r ^ 2 / 8).trans_le hstable.2)
    refine ⟨rightCovarianceField_analyticAt p (fun i => hU _ (hpsingle i))
      (fun i j => hfirst _ (thickening_subset_cthickening R _ (hppair i j)))
      (fun i j => hsecond _ (thickening_subset_cthickening R _ (hppair i j)))
      (fun i j => hsecondNe _ (thickening_subset_cthickening R _ (hppair i j))) hne,
      hstable.2, ?_⟩
    have hHbound (i j : Fin N) : ‖jointCovariancePair (p.1, p.2 i, p.2 j)‖ ≤ H * t ^ 2 * Δ :=
      covariancePair_shell_bound (thickening R (rightPairParameterSegment S))
        L K A L t Δ ρ hL.le hA.le hΔ.le hρΔ hΔt hLip
        q.1 p.1 (q.2 i) (p.2 i) (q.2 j) (p.2 j) (hqpair i i) (hppair i j)
        hparts.1 (hpcoord i) (hpcoord j) (hcoord i j) (hUv i)
        (hsecondInv _ (thickening_subset_cthickening R _ (hppair i j)))
    have hbnd := rightCovarianceField_norm_bound_general p L (H * t ^ 2 * Δ) (r ^ 2 / 8)
      hL.le (by positivity) (by positivity) (fun i => hUS _ (hpsingle i)) hHbound hstable.2
    apply hbnd.trans_eq
    rw [← htΔ]
    dsimp [B]
    field_simp [ht.ne', hΔ.ne']
  refine ⟨hall, ?_⟩
  intro k
  exact analytic_ball_joint_jet_bound k
    (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2) q ρ (B * (N : ℝ) ^ 2 / Δ) hρ
    (fun p hp => (hall p hp).1) (fun p hp => (hall p hp).2.2)


end IsingBulk.AnisoF002.Isotropic
