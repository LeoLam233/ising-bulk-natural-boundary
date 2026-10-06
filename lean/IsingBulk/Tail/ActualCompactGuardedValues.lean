import IsingBulk.Tail.ActualCompactGuardedJets
import IsingBulk.Tail.CompactGuardedPointwise
import IsingBulk.Tail.CompactSelectedLieDensity
import IsingBulk.Tail.CompactTruncatedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def compactGuardedLieCost (N M J : ℕ) (K G T : ℝ) : ℝ :=
  (2^(2*J)*T^(2*M)*compactPairWeightJetConstant N M J*G)*
    (1+(N:ℝ)*2^J*(K*(N:ℝ)^(2*(J+2))))^J

theorem compactGuardedLieCost_nonneg (N M J : ℕ) {K G T : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hT : 0 ≤ T) : 0 ≤ compactGuardedLieCost N M J K G T := by
  unfold compactGuardedLieCost compactPairWeightJetConstant
  positivity

/-- Near/far values of the actual guarded selected Lie operator. The only
numerator hypotheses are jet bounds subsequently supplied by the literal
sector-density theorems. Constants precede particle number and cutoff radius. -/
theorem actual_compact_guarded_regular_values (d₀ : LocalBranchData)
    (hcsmall : d₀.c₀ < Real.sin d₀.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d₀.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) (J : ℕ) :
    ∃ K G : ℝ, 0 < K ∧ 1 ≤ G ∧ ∀ᶠ H : ℝ in atTop,
      ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ P : Finset (Fin (n+1) × Fin (n+1)), ∀ M : ℕ, 0 < M → J ≤ M →
      ∀ i j : Fin (n+1), (i,j) ∈ P → i ≠ j → ∀ h : ℝ, 0 < h →
      ∀ θ : AngularSpace n,
      (∀ l, θ l ∈ Icc (-rightSectorRadius d₀.thetaB δ) (rightSectorRadius d₀.thetaB δ)) →
      θ i ≠ θ j → ∀ T : ℝ, 1 ≤ T → |θ i-θ j| ≤ T →
      let d := compactAllowedDiameter P θ
      let r := Real.exp (-d₀.c₀*Real.exp (-H))
      let s := radialParameter d₀.theta (Real.exp (-H))
      ∀ A : ℂ → AngularSpace n → ℂ, ParameterSmoothOn (compactSourceDomain (n+1) r) A →
      ∀ Cnear Cfar : ℝ, ∀ a : ℤ,
      (d ≤ 1 → RealScaledJetBound (Function.uncurry A) (s,θ) J d Cnear a) →
      RealScaledJetBound (Function.uncurry A) (s,θ) J 1 Cfar 0 →
      let F := ((lieStep (currentSelectedPairField f r τ lam i j))^[J]
        (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*A z x)) s θ
      (d ≤ 1 → ‖F‖ ≤ compactGuardedLieCost (n+1) M J K G T*Cnear*d^(a-2*(J:ℤ))) ∧
      ‖F‖ ≤ compactGuardedLieCost (n+1) M J K G T*Cfar*d^(-(2*M:ℕ):ℤ) := by
  obtain ⟨K,G,hK,hG,hjets⟩ := actual_compact_guarded_lie_jets d₀ hcsmall f hf hp1 hδ hδsmall hD hβ J
  refine ⟨K,G,hK,hG,?_⟩
  filter_upwards [hjets] with H hH
  intro n hND τ lam hτ hτ1 hlam hlamB P M hM hJM i j hij hne h hh θ hθ hgap T hT hgapT
    d r s A hA Cnear Cfar a hnear hfar F
  have hp := compactAllowedDiameter_pair_le P θ hij
  have hg : 0 < |θ i-θ j| := abs_pos.mpr (sub_ne_zero.mpr hgap)
  have hd : 0 < d := hg.trans_le hp
  have hall : ∀ q ∈ P, |θ q.1-θ q.2| ≤ d := fun _ hq => compactAllowedDiameter_pair_le P θ hq
  have hatt := compactAllowedDiameter_attained P θ hd
  constructor
  · intro hd1
    have hb := hH n hND τ lam hτ hτ1 hlam hlamB P M hM i j hij hne h hh θ hθ
      d |θ i-θ j| T (Cnear*d^a) hd hg (hp.trans hd1) hp hT hall hatt le_rfl
      (le_mul_of_one_le_left hg.le hT) A hA ((hnear hd1).smaller_scale hd hg hp) J le_rfl
    have hv := compact_guarded_near_value hb hd hg.le hp hJM
    exact hv.trans_eq (by unfold compactGuardedLieCost; ring)
  · let ρ := min 1 |θ i-θ j|
    have hρ : 0 < ρ := lt_min zero_lt_one hg
    have hρ1 : ρ ≤ 1 := min_le_left _ _
    have hρg : ρ ≤ |θ i-θ j| := min_le_right _ _
    have hsel : |θ i-θ j| ≤ T*ρ := by
      rcases le_total (1:ℝ) |θ i-θ j| with hg1|hg1
      · simpa only [ρ,min_eq_left hg1,mul_one] using hgapT
      · simpa only [ρ,min_eq_right hg1] using le_mul_of_one_le_left hg.le hT
    have hb := hH n hND τ lam hτ hτ1 hlam hlamB P M hM i j hij hne h hh θ hθ
      d ρ T Cfar hd hρ hρ1 (hρg.trans hp) hT hall hatt hρg hsel A hA
      (hfar.rescale_zero hρ hρ1) J le_rfl
    have hv := compact_guarded_far_value hb hρ.le hρ1 hJM
    exact hv.trans_eq (by unfold compactGuardedLieCost; ring)

theorem compact_guarded_pulled_factorization {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam h : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (hh : 0 < h)
    (P : Finset (Fin (n+1) × Fin (n+1))) (M : ℕ) {i j : Fin (n+1)} (hij : (i,j) ∈ P)
    (w : AngularSpace n → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ)
    {s : ℂ} {θ : AngularSpace n} (hp : (s,θ) ∈ compactSelectedDomain f r τ lam i j) :
    ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
      (fun z x => compactGuardedWeight P M h i j w x*pulledDensity f r τ lam z x)) s θ=
      mixedSimpleKernel f r τ lam s θ*
        ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
          (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*(w x*compactRegularDensity f r τ lam z x))) s θ := by
  have he := compact_selected_density_all_order f hf hr hr1 hτ hlam i j
    (compactGuardedWeight P M h i j w)
    (ParameterSmoothOn.angular _ _ (compactGuardedWeight_smooth P M hh hij w hw)) k hp
  have hfun : (fun z x => compactGuardedWeight P M h i j w x*compactRegularDensity f r τ lam z x)=
      (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*(w x*compactRegularDensity f r τ lam z x)) := by
    funext z x
    unfold compactGuardedWeight
    ring
  rwa [hfun] at he

end
end IsingBulk.Tail
