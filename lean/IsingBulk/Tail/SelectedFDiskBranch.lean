import IsingBulk.Tail.ProtectedBranchDisk

/-! The genuinely enlarged selected-F disk for true lower plateau roots.
Its radius is c/N, not c epsilon or c/N². Constants precede dimension,
occupancy and the actual coupled angular data. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem selected_disk_true_branch (d : LocalBranchData) :
    ∃ b r : ℝ, 0 < b ∧ 0 < r ∧ ∀ τ : ℝ, 0 < τ → τ < r →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (eps P u : ℝ) (s : ℂ),
        1 ≤ N → 0 < eps → eps < r → 1 ≤ P → P ≤ N → |u| < r →
        ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
        b*(eps+τ*(P/(N:ℝ))) ≤
          (sourceW s (plateauY d.c₀ eps τ (P/(N:ℝ)) d.thetaB u)).im ∧
        AnalyticAt ℂ (fun z => globalRoot z
          (plateauY d.c₀ eps τ (P/(N:ℝ)) d.thetaB u)) s := by
  let d₁ : LocalBranchData := { d with tau := 1, tau_pos := zero_lt_one }
  obtain ⟨b,C,r,hb,_,hr,hm⟩ := current_imaginary_margin d₁
  refine ⟨b/2,r,half_pos hb,hr,?_⟩
  intro τ hτ hτr
  let c := min (1/4:ℝ) (b*τ/12)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1/4 := min_le_left _ _
  have hcb : c ≤ b*τ/12 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro N eps P u s hN heps hepsr hP hPN hur hsd
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let t := P/(N:ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one hn0).mpr hPN
  have hτt : 0 ≤ τ*t := mul_nonneg hτ.le ht
  have hτtr : τ*t < r := (mul_le_of_le_one_right hτ.le ht1).trans_lt hτr
  have hcenter := (hm eps (τ*t) u heps hepsr hτt hτtr hur).1
  have hweq : currentW d₁ eps (τ*t) u =
      sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) := by
    rw [currentW_dispersion]
    simp only [d₁,plateauY,one_mul]
    rfl
  rw [hweq] at hcenter
  simp only [d₁,one_mul] at hcenter
  have hrad : c/(N:ℝ) ≤ c*t := by
    dsimp [t]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith) hn0.le
  have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
    have hct : c*t ≤ c := mul_le_of_le_one_right hc.le ht1
    linarith
  have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by
    rw [radialParameter_norm heps.le]
    linarith
  have hsn := norm_ge_half_of_near_unit hnorm hsmall
  have hs : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have htrace := sourceS_sub_norm_le hsn hnorm
  have hmove : ‖sourceW s (plateauY d.c₀ eps τ t d.thetaB u)-
      sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u)‖ ≤
      b*(eps+τ*t)/4 := by
    have heq : sourceW s (plateauY d.c₀ eps τ t d.thetaB u)-
        sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) =
        sourceS s-sourceS (radialParameter d.theta eps) := by unfold sourceW; ring
    rw [heq]
    have hct := mul_le_mul_of_nonneg_right hcb ht
    nlinarith
  obtain ⟨hmargin,hpos⟩ := protected_imaginary_margin hb heps hτt hcenter hmove
  refine ⟨?_,globalRoot_parameter_analyticAt hs hpos⟩
  change b/2*(eps+τ*t) ≤ _
  nlinarith

end
end IsingBulk.Tail
