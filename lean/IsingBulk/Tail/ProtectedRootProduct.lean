import IsingBulk.Tail.ProtectedBranchDisk
import IsingBulk.Tail.RootInflation
import IsingBulk.Tail.RootAttenuation

/-! Source-root assembly on protected disks. The remaining hypothesis is the
geometric compact/true-branch support cover, not a root-product estimate. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators

theorem protected_root_product (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ continuedRootDomain →
      ∀ σ : ℝ, 0 < σ → ∀ τ : ℝ, 0 < τ → τ < r →
      ∃ c cq : ℝ, 0 < c ∧ 0 < cq ∧
      ∀ (N : ℕ) (eps lamStar lam P θq : ℝ) (y : Fin N → ℂ) (q : Fin N) (s : ℂ),
        1 ≤ N → 0 < eps → eps < r → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
        1 ≤ P → P ≤ N → σ ≤ Real.sin θq →
        y q = upperAnchorY d.c₀ eps τ lam θq →
        (∀ i, 0 < (sourceW (radialParameter d.theta eps) (y i)).im) →
        sourceW (radialParameter d.theta eps) (y q) ∈ K →
        (∀ i, sourceW (radialParameter d.theta eps) (y i) ∈ K ∨
          ∃ u : ℝ, |u| < r ∧ y i=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u) →
        ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
        (∀ i, sourceW s (y i) ∈ continuedRootDomain) ∧
        ‖∏ i, continuedRoot (sourceW s (y i))‖ ≤ Real.exp (-(cq/2)*lam) := by
  obtain ⟨b,rB,hb,hrB,hbranch⟩ := protected_disk_true_branch d
  refine ⟨min rB 1,lt_min hrB zero_lt_one,?_⟩
  intro K hK hKD σ hσ
  obtain ⟨cR,L,hcR,hL,hproduct⟩ := continuedRoot_compact_branch_product hK hKD
  intro τ hτ hτr
  obtain ⟨cB,hcB,hbd⟩ := hbranch τ hτ (hτr.trans_le (min_le_left _ _))
  have hsin : 0 ≤ Real.sin d.theta :=
    (Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by have := d.theta_lt; linarith [Real.pi_pos])).le
  obtain ⟨cq,hcq,hanchor⟩ := upper_anchor_exponential_attenuation d.theta d.c₀_pos.le hτ hσ hsin
  let c := min cB (min (1/4:ℝ) (min (cR/3) (cq/(6*L))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB' : c ≤ cB := min_le_left _ _
  have hc1 : c ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcR' : c ≤ cR/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcqSlack : c ≤ cq/(6*L) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c,cq,hc,hcq,?_⟩
  intro N eps lamStar lam P θq y q s hN heps hepsr hls hl hl1 hP hPN hθq hyq hcenter hqK hcover hsd
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hn2 : 1 ≤ (N:ℝ)^2 := by nlinarith
  have hl0 : 0 < lam := hls.trans_le hl
  have heps1 : eps ≤ 1 := (hepsr.trans_le (min_le_right _ _)).le
  have hsdC : ‖s-radialParameter d.theta eps‖ ≤ c := by
    have h₁ : c*lamStar/(N:ℝ)^2 ≤ c*lamStar := div_le_self (by positivity) hn2
    have h₂ : c*lamStar ≤ c := mul_le_of_le_one_right hc.le (hl.trans hl1)
    exact hsd.trans (h₁.trans h₂)
  have hnorm0 : 1 ≤ ‖radialParameter d.theta eps‖ := by
    rw [radialParameter_norm heps.le]; linarith
  have hnorm := norm_ge_half_of_near_unit hnorm0 (show ‖s-radialParameter d.theta eps‖ < 1/2 by linarith)
  have htrace := sourceS_sub_norm_le hnorm hnorm0
  have hdiff (i : Fin N) :
      ‖sourceW s (y i)-sourceW (radialParameter d.theta eps) (y i)‖ ≤
        3*‖s-radialParameter d.theta eps‖ := by
    have he : sourceW s (y i)-sourceW (radialParameter d.theta eps) (y i)=
        sourceS s-sourceS (radialParameter d.theta eps) := by unfold sourceW; ring
    rw [he]
    exact htrace
  have hcover' (i : Fin N) : sourceW (radialParameter d.theta eps) (y i) ∈ K ∨
      0 < (sourceW s (y i)).im := by
    rcases hcover i with hk | ⟨u,hu,hyi⟩
    · exact Or.inl hk
    · right
      rw [hyi]
      have hdisc : ‖s-radialParameter d.theta eps‖ ≤ cB*lamStar/(N:ℝ)^2 :=
        hsd.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcB' hls.le) (sq_nonneg _))
      have h := (hbd N eps lamStar lam P u s hN heps
        (hepsr.trans_le (min_le_left _ _)) hls hl hl1 hP hPN
        (hu.trans_le (min_le_left _ _)) hdisc).1
      have ht : 0 ≤ lam*P/(N:ℝ) := by positivity
      exact lt_of_lt_of_le (by positivity) h
  have hanchor' : ‖continuedRoot (sourceW (radialParameter d.theta eps) (y q))‖ ≤
      Real.exp (-(cq*lam)) := by
    rw [continuedRoot_eq_interiorRoot (hcenter q),hyq]
    simpa [globalRoot,neg_mul] using hanchor eps lam θq heps.le heps1 hl0 hl1 hθq
  obtain ⟨hdom,hbound⟩ := hproduct N
    (fun i => sourceW (radialParameter d.theta eps) (y i)) (fun i => sourceW s (y i)) q
    (cq*lam) (3*‖s-radialParameter d.theta eps‖) (by positivity) (by linarith)
    hcenter hcover' hdiff hqK hanchor'
  refine ⟨hdom,hbound.trans (Real.exp_le_exp.mpr ?_)⟩
  have hden : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hdisc' : ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ) :=
    hsd.trans (div_le_div_of_nonneg_left (by positivity) hn0 hden)
  have hNdist := (le_div_iff₀ hn0).mp hdisc'
  have hNdist' : (N:ℝ)*‖s-radialParameter d.theta eps‖ ≤ c*lam := by
    have := mul_le_mul_of_nonneg_left hl hc.le
    nlinarith
  have hcmul := (le_div_iff₀ (show 0 < 6*L by positivity)).mp hcqSlack
  have h₁ := mul_le_mul_of_nonneg_left hNdist' (show 0 ≤ 3*L by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hcmul hl0.le
  nlinarith

end
end IsingBulk.Tail
