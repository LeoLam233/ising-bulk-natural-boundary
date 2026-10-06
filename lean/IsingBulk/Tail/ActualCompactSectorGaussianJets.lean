import IsingBulk.Tail.CompactSectorNumeratorJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1800000

theorem original_compact_sector_gaussian_jets (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 c e κ : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 < e ∧ 0 < κ ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
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
  obtain ⟨eta0,he0,hmain⟩ := original_compact_regular_gaussian_jets d hcsmall hmargin
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,c,e,κ,ha0,hc,he0',hκ,hjets⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,c,e,κ,ha0,hc,he0',hκ,?_⟩
  intro alpha ha haL outer inner ho hi J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  obtain ⟨δ,C,hδ,hC,hA⟩ := hjets alpha ha haL J
  obtain ⟨B,hB,hw⟩ := sector_joint_real_jets_common f hf d.thetaB outer inner ho hi J
  refine ⟨δ,2^J*B*C,hδ,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB) hC,?_⟩
  intro N hN eps τ heps hepsL hτ hτ1 s hs hsd hsmall θ hθ q sigma
  apply compact_sector_gaussian_product hN _ _ _ hB hC (hw N hN q sigma (s,θ)).1
  intro hsupp
  exact hA N hN eps τ heps hepsL hτ hτ1 s hs hsd hsmall θ hθ
    (original_sector_selector_support f d.thetaB outer inner ho hi q sigma hsupp)

theorem current_compact_sector_gaussian_jets (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∃ c e κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < κ ∧
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
  obtain ⟨eta0,he0,hmain⟩ := current_compact_regular_gaussian_jets d hcsmall hmargin
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1
  obtain ⟨c,e,κ,hc,he0',hκ,hjets⟩ := hsetup alpha tau ha haL ht htL ht1
  refine ⟨c,e,κ,hc,he0',hκ,?_⟩
  intro outer inner ho hi J
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  obtain ⟨δ,C,hδ,hC,hA⟩ := hjets J
  obtain ⟨B,hB,hw⟩ := sector_joint_real_jets_common f hf d.thetaB outer inner ho hi J
  refine ⟨δ,2^J*B*C,hδ,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB) hC,?_⟩
  intro N hN eps lam heps hepsL hlam hlam1 s hs hsd hsmall θ hθ qS q sigma
  apply compact_sector_gaussian_product hN _ _ _ hB hC ((hw N hN q sigma (s,θ)).2 tau ht.le ht1 qS)
  intro hsupp
  exact hA N hN eps lam heps hepsL hlam hlam1 s hs hsd hsmall θ hθ qS
    (current_sector_selector_support f tau d.thetaB outer inner ho hi qS q sigma hsupp)

end
end IsingBulk.Tail
