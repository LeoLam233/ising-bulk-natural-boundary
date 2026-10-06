import IsingBulk.Tail.PeriodicDeletedPairBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem original_actual_deleted_pairs_global (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 c e kappa : ℝ, ∃ B : ℕ → ℝ,
        0 < alpha0 ∧ 0 < c ∧ 0 < e ∧ (∀ j,0 < B j) ∧ 0 < kappa ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
        ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ)
          (E : Finset (Fin N × Fin N)) (j : ℕ),
          1 ≤ N → E.card ≤ j → 0 < eps → eps < e →
          θ ∈ tsupport (angularSelector (constructedSelector d.thetaB eta alpha)) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
          actualDeletedPairNorm (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*eps)) 0 0 s E θ ≤ (B j)^N*Real.exp (-kappa*(N:ℝ)^2) := by
  obtain ⟨eta0,he0,hmain⟩ := original_actual_source_deleted_pairs d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,c,e,kappa,B,ha0,hc,heps0,hB,hk,hb⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,c,e,kappa,B,ha0,hc,heps0,hB,hk,?_⟩
  intro alpha ha haL N eps θ s E j hN hE heps hepsL hsupp hsd hs
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hr1 : Real.exp (-d.c₀*eps) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  apply actual_deleted_pairs_all_angles (by omega : 0 < N) f hf (Real.exp_pos _) hr1
    le_rfl le_rfl hs E (angularSelector f) (angularSelector_periodic f hf)
    ((B j)^N*Real.exp (-kappa*(N:ℝ)^2)) _ θ hsupp
  intro x hx hxW
  have hh := hb alpha ha haL N eps x s E j hN hE heps hepsL hx hxW hsd
  simpa only [actualDeletedPairNorm,deformedPoint_zero,angleTuple] using hh

theorem current_actual_deleted_pairs_global (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 →
        ∃ c e kappa : ℝ, ∃ B : ℕ → ℝ,
          0 < c ∧ 0 < e ∧ (∀ j,0 < B j) ∧ 0 < kappa ∧
          ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ)
            (E : Finset (Fin N × Fin N)) (j : ℕ),
            E.card ≤ j → 1 ≤ N → 0 < eps → eps < e → 0 ≤ lam → lam ≤ 1 →
            θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB eta alpha) qidx) →
            ‖s-radialParameter d.theta eps‖ ≤ c*eps →
            s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
            actualDeletedPairNorm (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau lam s E θ ≤ (B j)^N*Real.exp (-kappa*(N:ℝ)^2) := by
  obtain ⟨eta0,he0,hmain⟩ := original_current_actual_source_deleted_pairs d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL
  obtain ⟨c,e,kappa,B,hc,heps0,hB,hk,hb⟩ := hsetup alpha tau ha haL ht htL
  refine ⟨c,e,kappa,B,hc,heps0,hB,hk,?_⟩
  intro N eps lam θ qidx s E j hE hN heps hepsL hlam hlam1 hsupp hsd hs
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hr1 : Real.exp (-d.c₀*eps) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  apply actual_deleted_pairs_all_angles (by omega : 0 < N) f hf (Real.exp_pos _) hr1 ht.le hlam hs E
    (namedSelectorDerivative f qidx) (namedSelectorDerivative_periodic f hf qidx)
    ((B j)^N*Real.exp (-kappa*(N:ℝ)^2)) _ θ hsupp
  intro x hx hxW
  exact hb N eps lam x qidx s E j hE hN heps hepsL hlam hlam1 hx hxW hsd

end
end IsingBulk.Tail
