import IsingBulk.Tail.CompactFreezingCoefficientJets
import IsingBulk.Tail.CompactSelectedWindow
import IsingBulk.Tail.RealScaledLieBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1800000

theorem selectedPairJetConstant_particle_scaling (J : ℕ) (C c n : ℝ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) :
    selectedPairJetConstant J (C*n^2) c = selectedPairJetConstant J C c*n^(2*(J+2)) := by
  have hCn : 1 ≤ C*n^2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hn)
  unfold selectedPairJetConstant
  rw [max_eq_right hCn,max_eq_right hC,mul_pow]
  have he : n^(2*(J+2))=n^2*n^2*(n^2)^J := by
    rw [pow_mul,pow_add,pow_two]
    ring
  rw [he]
  ring

/-- The actual selected field has polynomial particle cost and exactly the
simple-pole scale degree, uniformly on the source intermediate window. -/
theorem actual_compact_selected_field_jets (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) (J : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ i j l : Fin N, i ≠ j → ∀ θ : Fin N → ℝ,
      (∀ q, θ q ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ρ ≤ |θ i-θ j| →
      RealScaledJetBound
        (fun q : ℂ × (Fin N → ℝ) => currentSelectedPairField f
          (Real.exp (-d.c₀*Real.exp (-H))) τ lam i j q.1 q.2 l)
        (radialParameter d.theta (Real.exp (-H)),θ) J ρ (K*(N:ℝ)^(2*(J+2))) (-1) := by
  have hmargin := right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩
      ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  have hmpos : 0 < min (δ/2) ((1+Real.cos d.thetaB)/2) := lt_min (by linarith) (by linarith)
  have hstrict : ∀ a ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a| < 1 := fun a ha =>
    lt_of_le_of_lt (hmargin a ha) (by linarith)
  obtain ⟨r,C,hr,hC,hjets⟩ := actual_compact_freezing_coefficient_jets d f hf hp1 hstrict J
  obtain ⟨c,hc,hgap⟩ := actual_compact_selected_window d hcsmall f hf hp1 hδ hδsmall hD hβ
  let K := selectedPairJetConstant J C c
  have hK : 0 < K := by unfold K selectedPairJetConstant; positivity
  refine ⟨K,hK,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  have hden : 0 < 3+d.c₀ := by have := d.c₀_pos; positivity
  filter_upwards [hgap,ht.eventually (radial_source_eventually_damping d hcsmall),
    intermediate_window_current_small D β (r/(3+d.c₀)) hD hβ (div_pos hr hden),
    eventually_ge_atTop (0:ℝ)] with H hgapH hdom hsmall hH
  intro N hN hND τ lam hτ hτ1 hlam hlamB i j l hij θ hθ ρ hρ hρ1 hρgap
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlam1 : lam ≤ 1 := hlamB.trans (Real.exp_le_one_iff.mpr (by nlinarith))
  have hsmall' : ‖radialParameter d.theta (Real.exp (-H))-radialParameter d.theta 0‖+
      d.c₀*Real.exp (-H)+2*lam ≤ r := by
    rw [radialParameter_sub_zero_norm d.theta _ (Real.exp_pos _).le]
    have hh := hsmall N hND lam hlam hlamB
    have he : Real.exp (-H)+lam ≤ (N:ℝ)*(Real.exp (-H)+lam) :=
      le_mul_of_one_le_left (by positivity) hN1
    have hmul := (lt_div_iff₀ hden).mp (he.trans_lt hh)
    nlinarith [mul_nonneg d.c₀_pos.le hlam,Real.exp_pos (-H)]
  obtain ⟨hA,hQ,hDet⟩ := hjets N hN (Real.exp (-H)) τ lam (Real.exp_pos _) hτ hτ1 hlam hlam1
    (radialParameter d.theta (Real.exp (-H))) hdom.2.2 hsmall' θ hθ
  have hm := (hgapH N hN hND τ lam hτ hτ1 hlam hlamB i j hij θ hθ).1
  have hh := selected_pair_scaled_jets
    (fun k q => currentAngularLogYCoefficient f (Real.exp (-d.c₀*Real.exp (-H))) τ lam q.2 k)
    (fun q => currentPhaseParameterDerivative f (Real.exp (-d.c₀*Real.exp (-H))) τ lam q.1 q.2)
    (fun q => currentAngularDeterminant f (Real.exp (-d.c₀*Real.exp (-H))) τ lam q.1 i j q.2)
    (radialParameter d.theta (Real.exp (-H)),θ) i j l J ρ c (C*(N:ℝ)^2)
    hρ hρ1 hc hA hQ (hDet i j) ((mul_le_mul_of_nonneg_left hρgap hc.le).trans hm)
  rw [selectedPairJetConstant_particle_scaling J C c (N:ℝ) hC hN1] at hh
  exact hh

end
end IsingBulk.Tail
