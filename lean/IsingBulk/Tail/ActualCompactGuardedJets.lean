import IsingBulk.Tail.CompactGuardedLieJets
import IsingBulk.Tail.CompactSelectedQuantitative

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Actual source attachment of the guarded weighted Lie calculus. K and G
are fixed before N, the pair set, the cutoff radius and the selected pair. -/
theorem actual_compact_guarded_lie_jets (d₀ : LocalBranchData)
    (hcsmall : d₀.c₀ < Real.sin d₀.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d₀.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) (L : ℕ) :
    ∃ K G : ℝ, 0 < K ∧ 1 ≤ G ∧ ∀ᶠ H : ℝ in atTop,
      ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ P : Finset (Fin (n+1) × Fin (n+1)), ∀ M : ℕ, 0 < M →
      ∀ i j : Fin (n+1), (i,j) ∈ P → i ≠ j → ∀ h : ℝ, 0 < h →
      ∀ θ : AngularSpace n,
      (∀ l, θ l ∈ Icc (-rightSectorRadius d₀.thetaB δ) (rightSectorRadius d₀.thetaB δ)) →
      ∀ d ρ T C : ℝ, 0 < d → 0 < ρ → ρ ≤ 1 → ρ ≤ d → 1 ≤ T →
      (∀ q ∈ P, |θ q.1-θ q.2| ≤ d) → (∃ q ∈ P, |θ q.1-θ q.2|=d) →
      ρ ≤ |θ i-θ j| → |θ i-θ j| ≤ T*ρ →
      let r := Real.exp (-d₀.c₀*Real.exp (-H))
      let s := radialParameter d₀.theta (Real.exp (-H))
      ∀ A : ℂ → AngularSpace n → ℂ, ParameterSmoothOn (compactSourceDomain (n+1) r) A →
      RealScaledJetBound (Function.uncurry A) (s,θ) L ρ C 0 →
      ∀ k ≤ L, RealScaledJetBound
        (Function.uncurry ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
          (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*A z x)))
        (s,θ) (L-k) ρ
        ((2^(2*L)*T^(2*M)*compactPairWeightJetConstant (n+1) M L*G*C*d^(-(2*M:ℕ):ℤ))*
          (1+(n+1:ℕ)*2^L*(K*(n+1:ℕ)^(2*(L+2))))^k)
        ((2*M:ℕ)-2*(k:ℤ)) := by
  obtain ⟨K,hK,hfield⟩ := actual_compact_selected_field_jets d₀ hcsmall f hf hp1 hδ hδsmall hD hβ L
  obtain ⟨G,hG,hguard⟩ := compact_selected_guard_real_jets L
  obtain ⟨c,hc,hwindow⟩ := actual_compact_selected_window d₀ hcsmall f hf hp1 hδ hδsmall hD hβ
  refine ⟨K,G*2^L,hK,one_le_mul_of_one_le_of_one_le hG (one_le_pow₀ (by norm_num)),?_⟩
  filter_upwards [hfield,hwindow] with H hfieldH hwindowH
  intro n hND τ lam hτ hτ1 hlam hlamB P M hM i j hij hne h hh θ hθ d ρ T C
    hd hρ hρ1 hρd hT hp hatt hρgap hsel r s A hA hAb k hk
  have hgap : θ i ≠ θ j := sub_ne_zero.mp (abs_pos.mp (hρ.trans_le hρgap))
  have hpoint := (hwindowH (n+1) (Nat.succ_pos n) hND τ lam hτ hτ1 hlam hlamB i j hne θ hθ).2 hgap
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d₀.c₀_pos,Real.exp_pos (-H)])
  let Ω := compactSelectedDomain f r τ lam i j ∩ {q : ℂ × AngularSpace n | compactPairWeightDenom P M q.2 ≠ 0}
  have hΩ : IsOpen Ω := (compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j).inter
    (isOpen_ne_fun ((compactPairWeightDenom_smooth P M).continuous.comp continuous_snd) continuous_const)
  have hpΩ : (s,θ) ∈ Ω := ⟨hpoint,(compactPairWeightDenom_selected_pos P M hij hgap).ne'⟩
  apply compact_guarded_weighted_lie_jets hΩ _ A P M L hM i j h
    (fun l p hp => currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j l p hp.1)
    (fun p hp => hA p hp.1.1) (fun _ hp => hp.2) hpΩ hd hρ hρ1 hρd hT
    (mul_nonneg hK.le (by positivity)) le_rfl hp hatt hsel
    (fun l => hfieldH (n+1) (Nat.succ_pos n) hND τ lam hτ hτ1 hlam hlamB i j l hne θ hθ ρ hρ hρ1 hρgap)
    hAb (hguard (n+1) h hh i j (s,θ) ρ hρ hρgap) k hk

end
end IsingBulk.Tail
