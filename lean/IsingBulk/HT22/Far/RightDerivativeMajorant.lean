import IsingBulk.HT22.Far.RightDerivativeTail

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- A summable per-particle majorant, independent of epsilon and both signs.
Unlike a bound only on the total sum, this explicitly provides uniform
particle tails on every compact positive radial interval. -/
theorem actual_high_right_derivative_majorant (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ : ℝ, δ≤δB → ∀ rcut : ℝ → ℝ, PreferredRightCutoffData b B δ rcut →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∃ W : ℕ → ℝ, Summable W ∧ (∀ n,0≤W n) ∧
    ∀ negative : Bool, ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ n : ℕ,
    ‖iteratedDeriv j
      (Physical.rightPopulationIntegral negative (2*(p/2+n)+2) τ preferredPopulationCutoff B.p B.m rcut)
      (IsingBulk.Branch.radialParameter b.alpha ε)‖≤W n*(1+|Real.log ε|) := by
  obtain ⟨capM,hcapM,hcapMa,hmass⟩ := actual_whole_angular_mass b
  obtain ⟨capI,hcapI,hcapIa,hidentity⟩ := actual_right_integral_identity b
  refine ⟨min capM capI,lt_min hcapM hcapI,(min_le_left _ _).trans_lt hcapMa,?_⟩
  intro B hB
  obtain ⟨eM,tM,dM,heM,htM,hdM,hdMB,hmass⟩ := hmass B (hB.trans_le (min_le_left _ _))
  obtain ⟨eI,tI,dI,heI,htI,hdI,hdIB,hidentity⟩ := hidentity B (hB.trans_le (min_le_right _ _))
  refine ⟨min eM eI,min tM tI,min dM dI,lt_min heM heI,lt_min htM htI,
    lt_min hdM hdI,(min_le_left _ _).trans_lt hdMB,?_⟩
  intro δ hδ rcut hcut p hp5 hp j hj
  obtain ⟨H,A,L,hH,hA,hmass⟩ := hmass rcut hcut.2.2.1 hcut.2.2.2.1 j
  let W : ℕ → ℝ := fun n => completeOrderEnvelope H A L (2*(p/2+n)+3)
  have hW (n : ℕ) : 0≤W n := completeOrderEnvelope_nonneg hH.le hA.le _ _
  have hsum : Summable W := (completeOrderEnvelope_summable H hA.le L).comp_injective
    (by intro n m h; change 2*(p/2+n)+3=2*(p/2+m)+3 at h;omega)
  refine ⟨W,hsum,hW,?_⟩
  intro negative ε τ hε hεr hτ hτr n
  have hdeg := high_odd_transport_degree hp5 hp n
  have hm := hmass (Physical.constraintAngle negative) (Physical.constraintAngle negative)
    (constraintAngle_abs_le_pi negative) (p/2+n) (by omega) ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) δ (hδ.trans (min_le_left _ _)) hcut
  have hi := hidentity δ (hδ.trans (min_le_right _ _)) rcut hcut
    (IsingBulk.HT.First.derivativeOrder p) (p/2+n) hdeg
    negative τ hτ (hτr.trans_le (min_le_right _ _)) j hj ε hε (hεr.trans_le (min_le_right _ _))
  rw [hi,←wholeTransportedIntegral_physical]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  change (wholeTransportedMass b B rcut j (Physical.constraintAngle negative)
    (Physical.constraintAngle negative) (p/2+n) ε τ).toReal≤
    (ENNReal.ofReal (W n*(1+|Real.log ε|))).toReal at hh
  rw [ENNReal.toReal_ofReal (mul_nonneg (hW n) (by positivity))] at hh
  exact (norm_integral_le_lintegral_norm _).trans hh

end
end IsingBulk.HT22.Far
