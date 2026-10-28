import IsingBulk.HT22.Far.PhysicalTailBridge
import IsingBulk.HT22.Tail.ActualIntegralIdentity

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem high_odd_transport_degree {p : ℕ} (hp5 : 5≤p) (hp : Odd p) (n : ℕ) :
    2*IsingBulk.HT.First.derivativeOrder p+9≤(2*(p/2+n)+3)^2 := by
  have hh := full_shell_exponent hp (high_odd_order_ge hp n)
    (le_refl (IsingBulk.HT.First.derivativeOrder p))
  omega

/-- Uniform absolute summation of the ORIGINAL signed right-coefficient
complex derivatives, not a conditional transported scalar surrogate. -/
theorem actual_high_right_derivative_sum (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ : ℝ, δ≤δB → ∀ rcut : ℝ → ℝ, PreferredRightCutoffData b B δ rcut →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∃ C : ℝ, 0<C ∧ ∀ negative : Bool, ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
    Summable (fun n => ‖iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε)‖) ∧
    (∑' n,‖iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε)‖)≤C*(1+|Real.log ε|) := by
  obtain ⟨capM,hcapM,hcapMa,hmass⟩ := actual_high_odd_mass_sum b
  obtain ⟨capI,hcapI,hcapIa,hidentity⟩ := actual_right_integral_identity b
  refine ⟨min capM capI,lt_min hcapM hcapI,(min_le_left _ _).trans_lt hcapMa,?_⟩
  intro B hB
  obtain ⟨eM,tM,dM,heM,htM,hdM,hdMB,hmass⟩ := hmass B (hB.trans_le (min_le_left _ _))
  obtain ⟨eI,tI,dI,heI,htI,hdI,hdIB,hidentity⟩ := hidentity B (hB.trans_le (min_le_right _ _))
  refine ⟨min eM eI,min tM tI,min dM dI,lt_min heM heI,lt_min htM htI,
    lt_min hdM hdI,(min_le_left _ _).trans_lt hdMB,?_⟩
  intro δ hδ rcut hcut p hp5 hp j hj
  obtain ⟨C,hC,hmass⟩ := hmass rcut hcut.2.2.1 hcut.2.2.2.1 p hp5 hp j hj
  refine ⟨C,hC,?_⟩
  intro negative ε τ hε hεr hτ hτr
  have hm := (hmass (Physical.constraintAngle negative) (Physical.constraintAngle negative)
    (constraintAngle_abs_le_pi negative) ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) δ (hδ.trans (min_le_left _ _)) hcut).2
  have heq (n : ℕ) : iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε)=
      wholeTransportedIntegral b B rcut j (Physical.constraintAngle negative)
        (Physical.constraintAngle negative) (p/2+n) ε τ := by
    rw [wholeTransportedIntegral_physical]
    exact hidentity δ (hδ.trans (min_le_right _ _)) rcut hcut
      (IsingBulk.HT.First.derivativeOrder p) (p/2+n) (high_odd_transport_degree hp5 hp n)
      negative τ hτ (hτr.trans_le (min_le_right _ _)) j hj ε hε (hεr.trans_le (min_le_right _ _))
  simp_rw [heq]
  exact hm

/-- The full original high odd right-derivative sum is lower order than
ε⁻¹, with no finite-N truncation or unproved interchange of limits. -/
theorem actual_high_right_derivative_epsilon_zero (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ : ℝ, δ≤δB → ∀ rcut : ℝ → ℝ, PreferredRightCutoffData b B δ rcut →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∀ negative : Bool, ∀ τ : ℝ, 0≤τ → τ<τ₀ →
    Tendsto (fun ε : ℝ => ε*(∑' n,‖iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε)‖)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => (ε:ℂ)*(∑' n,iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_high_right_derivative_sum b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro δ hδ rcut hcut p hp5 hp j hj negative τ hτ hτr
  obtain ⟨C,_hC,hsource⟩ := hsource δ hδ rcut hcut p hp5 hp j hj
  have hb (ε : ℝ) (hε : 0<ε) (hεr : ε<e) := hsource negative ε τ hε hεr hτ hτr
  constructor
  · apply epsilon_zero_of_log_bound _ he
    intro ε hε hεr
    exact ⟨tsum_nonneg (fun _ => norm_nonneg _),(hb ε hε hεr).2⟩
  · exact complex_epsilon_zero_of_absolute_log_bound _ he hb

end
end IsingBulk.HT22.Far
