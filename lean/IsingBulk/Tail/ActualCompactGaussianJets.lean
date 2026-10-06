import IsingBulk.Tail.CompactGaussianNumeratorJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem compact_gaussian_jet_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} {N J : ℕ} (hN : 0 < N) {C B κ : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    (h : RealScaledJetBound f x J 1
      (2^J*C^(N+J)*(N:ℝ)^(5*J)*(B^N*Real.exp (-κ*(N:ℝ)^2))) 0) :
    RealScaledJetBound f x J 1
      ((2^J*C^(J+1)*max 1 B)^N*(N:ℝ)^(5*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  apply h.mono zero_lt_one le_rfl
  have hh := mul_le_mul_of_nonneg_right (compact_gaussian_cost_absorption (J := J) hN hC hB)
    (by positivity : 0 ≤ (N:ℝ)^(5*J)*Real.exp (-κ*(N:ℝ)^2))
  convert hh using 1 <;> ring

/-- The Gaussian rate is fixed before derivative order. The estimate controls
the actual original numerator on signed compact-right source angles. -/
theorem original_compact_regular_gaussian_jets (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 c e κ : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 < e ∧ 0 < κ ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 → ∀ J : ℕ,
      ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
        ∀ eps τ : ℝ, 0 < eps → eps < e → 0 ≤ τ → τ ≤ 1 →
        ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        ‖s-radialParameter d.theta 0‖+d.c₀*eps ≤ δ →
        ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) →
        θ ∈ tsupport (angularSelector (constructedSelector d.thetaB eta alpha)) →
        RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
          compactRegularDensity (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) τ 0 q.1 q.2)
          (s,θ) J 1 (C^N*(N:ℝ)^(5*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  obtain ⟨eta0,he0,hmain⟩ := original_actual_deleted_pairs_global d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,c,e,κ,B,ha0,hc,he0',hB,hκ,hpairs⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,c,e,κ,ha0,hc,he0',hκ,?_⟩
  intro alpha ha haL J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨δ,C,hδ,hC,hjets⟩ := actual_compact_regular_numerator_deleted_jets d f hf hp1 hmargin J
  refine ⟨δ,2^J*C^(J+1)*max 1 (B J),hδ,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hC)) (le_max_left _ _)
  intro N hN eps τ heps hepsL hτ hτ1 s hs hsd hsmall θ hθ hsupp
  apply compact_gaussian_jet_cost hN hC (hB J).le
  apply hjets N hN eps τ 0 heps hτ hτ1 le_rfl zero_le_one s hs
    (by simpa only [mul_zero,add_zero] using hsmall) θ hθ _
    (mul_nonneg (pow_nonneg (hB J).le _) (Real.exp_pos _).le)
  intro E hE hEJ
  have hh := hpairs alpha ha haL N eps θ s E J (by omega) hEJ heps hepsL hsupp hsd hs
  simpa only [actualDeletedPairNorm,deformedPoint_zero] using hh

/-- All lambda in the small-current range inherit the unchanged Gaussian
rate before J is chosen; the full named support is retained. -/
theorem current_compact_regular_gaussian_jets (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∃ c e κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < κ ∧ ∀ J : ℕ,
        ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
          ∀ eps lam : ℝ, 0 < eps → eps < e → 0 ≤ lam → lam ≤ 1 →
          ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
          ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) → ∀ qidx : Fin N,
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB eta alpha) qidx) →
          RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
            compactRegularDensity (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau lam q.1 q.2)
            (s,θ) J 1 (C^N*(N:ℝ)^(5*J)*Real.exp (-κ*(N:ℝ)^2)) 0 := by
  obtain ⟨eta0,he0,hmain⟩ := current_actual_deleted_pairs_global d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1
  obtain ⟨c,e,κ,B,hc,he0',hB,hκ,hpairs⟩ := hsetup alpha tau ha haL ht htL
  refine ⟨c,e,κ,hc,he0',hκ,?_⟩
  intro J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨δ,C,hδ,hC,hjets⟩ := actual_compact_regular_numerator_deleted_jets d f hf hp1 hmargin J
  refine ⟨δ,2^J*C^(J+1)*max 1 (B J),hδ,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hC)) (le_max_left _ _)
  intro N hN eps lam heps hepsL hlam hlam1 s hs hsd hsmall θ hθ qidx hsupp
  apply compact_gaussian_jet_cost hN hC (hB J).le
  apply hjets N hN eps tau lam heps ht.le ht1 hlam hlam1 s hs hsmall θ hθ _
    (mul_nonneg (pow_nonneg (hB J).le _) (Real.exp_pos _).le)
  intro E hE hEJ
  exact hpairs N eps lam θ qidx s E J hEJ (by omega) heps hepsL hlam hlam1 hsupp hsd hs

end
end IsingBulk.Tail
