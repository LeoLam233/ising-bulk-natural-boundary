import IsingBulk.Tail.CompactRightActualCurvature
import IsingBulk.Tail.IntermediateWindow

/-! Uniform actual compact-right curvature on the intermediate window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- The threshold is chosen before N and before the actual homotopy value. -/
theorem intermediate_window_current_small (D β b : ℝ)
    (hD : 0≤D) (hβ : 0<β) (hb : 0<b) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, (N:ℝ)≤D*Real.sqrt H →
      ∀ lam : ℝ, 0≤lam → lam≤Real.exp (-β*H) →
      (N:ℝ)*(Real.exp (-H)+lam)<b := by
  filter_upwards [intermediate_window_uniform_small D 0 1 1 hD le_rfl zero_lt_one (b/2) (half_pos hb),
    intermediate_window_uniform_small D 0 β 1 hD le_rfl hβ (b/2) (half_pos hb)] with H h1 h2
  intro N hN lam _ hlam
  have hh1 := h1 N hN
  have hh2 := h2 N hN
  simp only [zero_mul,Real.exp_zero,mul_one,pow_one,neg_mul,one_mul] at hh1 hh2
  have hh := mul_le_mul_of_nonneg_left hlam (Nat.cast_nonneg N)
  simp only [neg_mul] at hh
  nlinarith

theorem actual_compact_right_window_curvature (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ k : ℝ, 0<k ∧ ∀ᶠ H : ℝ in atTop, ∀ (N : ℕ), 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ (τ lam : ℝ) (θ v : Fin N → ℝ) (t : ℝ), 0≤τ → τ≤1 →
      0≤lam → lam≤Real.exp (-β*H) → ‖v‖≤1 → 1≤∑ i, (v i)^2 →
      (∀ i, (θ+t • v) i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      deriv (deriv (fun u => currentUnwrappedPhase f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H))) (θ+u • v))) t ≤ -k := by
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  let k := (1+Real.cos d.thetaB)*min (δ/2) ((1+Real.cos d.thetaB)/2)/2
  have hk : 0<k := by dsimp [k]; positivity
  obtain ⟨r,C,hr,hC,hbound⟩ := actual_compact_right_direction_curvature d hcsmall f hf hp1 hδ hδsmall
  refine ⟨k,hk,?_⟩
  filter_upwards [intermediate_window_current_small D β (min r (k/C)) hD hβ
    (lt_min hr (div_pos hk hC)),eventually_ge_atTop (0:ℝ)] with H hsmall hH
  intro N hN hND τ lam θ v t hτ hτ1 hlam hlamB hv hv2 hθ
  have hNs : (1:ℝ)≤N := by exact_mod_cast hN
  have hs := hsmall N hND lam hlam hlamB
  have heps := Real.exp_pos (-H)
  have hsmallR : Real.exp (-H)+lam≤r := by
    have hh := hs.trans_le (min_le_left _ _)
    nlinarith
  have hlam1 : lam≤1 := hlamB.trans (Real.exp_le_one_iff.mpr (by nlinarith))
  have hb := hbound N hN (Real.exp (-H)) τ lam θ v t heps hτ hτ1 hlam hlam1 hv hv2 hθ hsmallR
  have herr : (N:ℝ)*C*(Real.exp (-H)+lam)<k := by
    have hh := hs.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ hC).mp hh
    nlinarith only [hh']
  dsimp [k] at hk ⊢
  dsimp [k] at herr
  linarith

end
end IsingBulk.Tail
