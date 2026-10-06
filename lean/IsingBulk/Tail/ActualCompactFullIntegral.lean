import IsingBulk.Tail.ActualCompactPairIntegral
import IsingBulk.Tail.CompactPairReconstruction

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

/-- Full compact source bound after finite pair reconstruction. The remaining
near exponent is the literal pair count minus the proved Lie/coarea losses. -/
theorem actual_compact_full_integral_bound (d₀ : LocalBranchData)
    (hcsmall : d₀.c₀ < Real.sin d₀.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ τ D β : ℝ} (hδ : 0 < δ)
    (hδsmall : δ < 2*(1-Real.cos d₀.thetaB)) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hD : 0 ≤ D) (hβ : 0 < β) (J : ℕ) :
    ∃ K G Q : ℝ, 0 < K ∧ 1 ≤ G ∧ 0 < Q ∧ ∀ᶠ H : ℝ in atTop,
      ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ P : Finset (Fin (n+1) × Fin (n+1)), P ⊆ orderedIndexPairs Finset.univ →
      2*J+1 ≤ 2*P.card →
      let R := rightSectorRadius d₀.thetaB δ
      let S := Icc (fun _ : Fin (n+1) => -R) (fun _ => R)
      let r := Real.exp (-d₀.c₀*Real.exp (-H))
      let s := radialParameter d₀.theta (Real.exp (-H))
      ∀ w : AngularSpace n → ℂ, ContDiff ℝ ∞ w → tsupport w ⊆ S →
      ∀ Cnear Cfar ρ : ℝ, 0 ≤ Cnear → 0 ≤ Cfar → 0 < ρ → ρ ≤ 1 →
      (∀ θ ∈ S, 0 < compactAllowedDiameter P θ → compactAllowedDiameter P θ ≤ 1 →
        RealScaledJetBound (fun p : ℂ × AngularSpace n => w p.2*compactRegularDensity f r τ lam p.1 p.2)
          (s,θ) J (compactAllowedDiameter P θ) Cnear (2*(P.card:ℤ))) →
      (∀ θ ∈ S, RealScaledJetBound
        (fun p : ℂ × AngularSpace n => w p.2*compactRegularDensity f r τ lam p.1 p.2) (s,θ) J 1 Cfar 0) →
      ‖iteratedDeriv J (fun z => ∫ θ, w θ*pulledDensity f r τ lam z θ) s‖ ≤
        (4*compactGuardedLieCost (n+1) (J+1) J K G (max 1 (2*R)))*
          (Cnear*ρ^(2*P.card-2*J-1)+Cfar*ρ^(-(2*(J+1)+1:ℕ):ℤ))*(Q^(n+1)*(n+1:ℕ)^6*(H+1)^2) := by
  obtain ⟨K,G,Q,hK,hG,hQ,hpair⟩ := actual_compact_pair_integral_bound d₀ hcsmall f hf hp1
    hδ hδsmall hτ hτ1 hD hβ J
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  refine ⟨K,G,Q,hK,hG,hQ,?_⟩
  filter_upwards [hpair,ht.eventually (radial_source_eventually_damping d₀ hcsmall)] with H hpH hdom
  intro n hND lam hlam hlamB P hP hdeg R S r s w hw hsupp Cnear Cfar ρ hCn hCf hρ hρ1 hnear hfar
  have hdiff (p) (hp : p ∈ P) : p.1 ≠ p.2 := (Finset.mem_filter.mp (hP hp)).2.ne
  have hnon : ∃ p ∈ P, p.1 ≠ p.2 := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
    exact ⟨p,hp,hdiff p hp⟩
  have hdegree : 2*(P.card:ℤ)=2*(J:ℤ)+((2*P.card-2*J-1+1:ℕ):ℤ) := by omega
  have hnear' (θ) (hθ : θ ∈ S) (hd : 0 < compactAllowedDiameter P θ) (hd1 : compactAllowedDiameter P θ ≤ 1) :=
    hnear θ hθ hd hd1
  simp_rw [hdegree] at hnear'
  have hh := compact_pair_derivative_bound f hf hdom.1 hdom.2.1 hτ hlam P (J+1) hnon w hw
    (isCompact_Icc.of_isClosed_subset isClosed_closure hsupp) J hdom.2.2
    (B := (4*compactGuardedLieCost (n+1) (J+1) J K G (max 1 (2*R)))*
      (Cnear*ρ^(2*P.card-2*J-1)+Cfar*ρ^(-(2*(J+1)+1:ℕ):ℤ))*(Q^(n+1)*(n+1:ℕ)^4*(H+1)^2))
    (by
      have hc := compactGuardedLieCost_nonneg (n+1) (J+1) J hK.le (show 0 ≤ G by linarith)
        (show 0 ≤ max 1 (2*R) from zero_le_one.trans (le_max_left _ _))
      positivity)
    (fun p hp => hpH n hND lam hlam hlamB P (J+1) (by omega) (by omega) p.1 p.2 hp (hdiff p hp)
      w hw hsupp Cnear Cfar ρ hCn hCf hρ hρ1 (2*P.card-2*J-1) hnear' hfar)
  exact hh.trans_eq (by ring)

end
end IsingBulk.Tail
