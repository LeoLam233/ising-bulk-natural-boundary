import IsingBulk.Tail.ActualCompactSectorGaussianJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Selector thresholds and the Gaussian rate precede the compact interval.
Only the finite-jet constant and local source radius use its margin. -/
theorem original_compact_sector_gaussian_jets_uniform (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 c e κ : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 < e ∧ 0 < κ ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
      ∀ a b : ℝ, (∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) →
      ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ),
      ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
        ∀ eps τ : ℝ, 0 < eps → eps < e → 0 ≤ τ → τ ≤ 1 →
        ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        ‖s-radialParameter d.theta 0‖+d.c₀*eps ≤ δ →
        ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ q : Fin N, ∀ sigma : Fin N → Fin 3,
        let f := constructedSelector d.thetaB eta alpha
        RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
          originalSectorAngularWeight f d.thetaB outer inner ho hi q sigma z.2*
            compactRegularDensity f (Real.exp (-d.c₀*eps)) τ 0 z.1 z.2)
          (s,θ) J 1 (C^N*(N:ℝ)^(6*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  obtain ⟨eta0,he0,hmain⟩ := original_actual_deleted_pairs_global d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,c,e,κ,B,ha0,hc,he0',hB,hκ,hpairs⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,c,e,κ,ha0,hc,he0',hκ,?_⟩
  intro alpha ha haL a b hmargin outer inner ho hi J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨δ,C,hδ,hC,hjets⟩ := actual_compact_regular_numerator_deleted_jets d f hf hp1 hmargin J
  obtain ⟨W,hW,hw⟩ := sector_joint_real_jets_common f hf d.thetaB outer inner ho hi J
  let C₁ := 2^J*C^(J+1)*max 1 (B J)
  have hC₁ : 1 ≤ C₁ := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hC)) (le_max_left _ _)
  refine ⟨δ,2^J*W*C₁,hδ,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hW) hC₁,?_⟩
  intro N hN eps τ heps hepsL hτ hτ1 s hs hsd hsmall θ hθ q sigma
  apply compact_sector_gaussian_product hN _ _ _ hW hC₁ (hw N hN q sigma (s,θ)).1
  intro hsupp
  apply compact_gaussian_jet_cost hN hC (hB J).le
  apply hjets N hN eps τ 0 heps hτ hτ1 le_rfl zero_le_one s hs
    (by simpa only [mul_zero,add_zero] using hsmall) θ hθ _ (by positivity [hB J])
  intro E hE hEJ
  have hh := hpairs alpha ha haL N eps θ s E J (by omega) hEJ heps hepsL
    (original_sector_selector_support f d.thetaB outer inner ho hi q sigma hsupp) hsd hs
  simpa only [actualDeletedPairNorm,deformedPoint_zero] using hh

theorem current_compact_sector_gaussian_jets_uniform (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∃ c e κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < κ ∧
        ∀ a b : ℝ, (∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (J : ℕ),
        ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
          ∀ eps lam : ℝ, 0 < eps → eps < e → 0 ≤ lam → lam ≤ 1 →
          ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
          ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ qS q : Fin N, ∀ sigma : Fin N → Fin 3,
          let f := constructedSelector d.thetaB eta alpha
          RealScaledJetBound (fun z : ℂ × (Fin N → ℝ) =>
            currentSectorAngularWeight f tau qS d.thetaB outer inner ho hi q sigma z.2*
              compactRegularDensity f (Real.exp (-d.c₀*eps)) tau lam z.1 z.2)
            (s,θ) J 1 (C^N*(N:ℝ)^(6*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  obtain ⟨eta0,he0,hmain⟩ := current_actual_deleted_pairs_global d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1
  obtain ⟨c,e,κ,B,hc,he0',hB,hκ,hpairs⟩ := hsetup alpha tau ha haL ht htL
  refine ⟨c,e,κ,hc,he0',hκ,?_⟩
  intro a b hmargin outer inner ho hi J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨δ,C,hδ,hC,hjets⟩ := actual_compact_regular_numerator_deleted_jets d f hf hp1 hmargin J
  obtain ⟨W,hW,hw⟩ := sector_joint_real_jets_common f hf d.thetaB outer inner ho hi J
  let C₁ := 2^J*C^(J+1)*max 1 (B J)
  have hC₁ : 1 ≤ C₁ := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hC)) (le_max_left _ _)
  refine ⟨δ,2^J*W*C₁,hδ,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hW) hC₁,?_⟩
  intro N hN eps lam heps hepsL hlam hlam1 s hs hsd hsmall θ hθ qS q sigma
  apply compact_sector_gaussian_product hN _ _ _ hW hC₁ ((hw N hN q sigma (s,θ)).2 tau ht.le ht1 qS)
  intro hsupp
  apply compact_gaussian_jet_cost hN hC (hB J).le
  apply hjets N hN eps tau lam heps ht.le ht1 hlam hlam1 s hs hsmall θ hθ _ (by positivity [hB J])
  intro E hE hEJ
  exact hpairs N eps lam θ qS s E J hEJ (by omega) heps hepsL hlam hlam1
    (current_sector_selector_support f tau d.thetaB outer inner ho hi qS q sigma hsupp) hsd hs

end
end IsingBulk.Tail
