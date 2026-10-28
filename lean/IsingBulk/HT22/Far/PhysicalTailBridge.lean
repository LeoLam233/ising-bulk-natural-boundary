import IsingBulk.HT22.Far.TailLimit
import IsingBulk.HT22.Tail.PhysicalSigns

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem wholeTransportedIntegral_physical (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (rcut : ℝ → ℝ) (j : ℕ) (negative : Bool) (n : ℕ) (ε τ : ℝ) :
    wholeTransportedIntegral b B rcut j (Physical.constraintAngle negative)
      (Physical.constraintAngle negative) n ε τ=
    transportedIntegral negative (2*n+2) B.delta τ preferredPopulationCutoff B.p B.m rcut j
      (IsingBulk.Branch.radialParameter b.alpha ε) := by
  unfold wholeTransportedIntegral transportedIntegral
  rw [constraintSign_eq_signed_exp]
  rfl

theorem actual_high_signed_epsilon_zero (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∀ negative : Bool, ∀ τ : ℝ, 0≤τ → τ<τ₀ →
    ∀ δ : ℝ, δ≤δB → PreferredRightCutoffData b B δ rcut →
    Tendsto (fun ε : ℝ => ε*(∑' n,‖transportedIntegral negative (2*(p/2+n)+2) B.delta τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)‖))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => (ε:ℂ)*(∑' n,transportedIntegral negative (2*(p/2+n)+2) B.delta τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_high_odd_epsilon_zero b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hrper p hp5 hp j hj negative τ hτ hτr δ hδ hcut
  simpa only [wholeTransportedIntegral_physical] using
    hsource rcut hrcut hrper p hp5 hp j hj (Physical.constraintAngle negative)
      (Physical.constraintAngle negative) (constraintAngle_abs_le_pi negative) τ hτ hτr δ hδ hcut

end
end IsingBulk.HT22.Far
