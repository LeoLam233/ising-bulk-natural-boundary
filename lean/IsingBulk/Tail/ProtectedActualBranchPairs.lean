import IsingBulk.Tail.ProtectedBranchPair
import IsingBulk.Tail.ProtectedActualPairs

/-! Actual source-coordinate attachment of the strict lower-branch complete
pair estimate. The fixed branch width is chosen before selector eta. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem protected_actual_branch_pair_bound (d : LocalBranchData) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c e : ℝ, 0 < c ∧ 0 < e ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < e → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N → θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
          ∀ i j, lowerChord d.thetaB (θ i) < η^2/2 → lowerChord d.thetaB (θ j) < η^2/2 →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          ‖canceledPair (y i) (y j) (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j))‖ ≤ 1/2 := by
  obtain ⟨r,hr,hB⟩ := protected_lower_branch_complete_pair d (q := 1/2) (by norm_num)
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  refine ⟨min ηA (Real.sin d.thetaB/4),r,lt_min hηA (by positivity [d.a_pos]),hr,?_⟩
  intro η α τ hη hηlt hα _hαsmall hτ hτlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  have hηA' := hηlt.le.trans (min_le_left _ _)
  obtain ⟨c,hc,hpair⟩ := hB τ hτ hτlt
  refine ⟨c,r,hc,hr,?_⟩
  intro N eps lamStar lam θ q s hN heps hepsr hls hl hl1 hθ hsupp hsd i j hi hj
  let f := constructedSelector d.thetaB η α
  let P := occupancy (fun i => f.p (θ i))
  obtain ⟨hqp,_,_,_,_⟩ := constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα q hsupp
  have hP : 1 ≤ P := occupancy_named (fun i => (thresholdStep_range _ _ _).1) q hqp
  have hPN : P ≤ N := occupancy_le (fun i => (thresholdStep_range _ _ _).2)
  have hcore (k : Fin N) (hk : lowerChord d.thetaB (θ k) < η^2/2) :
      |θ k+d.thetaB-2*Real.pi| < r ∧
      deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ k =
        plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB (θ k+d.thetaB-2*Real.pi) := by
    have hch : lowerChord d.thetaB (θ k) ≤ η^2 := by linarith [sq_nonneg η]
    obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau d.a_pos hη hηsmall hα hch
    refine ⟨hcoord (θ k) (hθ.1 k) (hθ.2 k) (hch.trans (pow_le_pow_left₀ hη.le hηA' 2)),?_⟩
    exact deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ k hpi hmi
  obtain ⟨hui,hyi⟩ := hcore i hi
  obtain ⟨huj,hyj⟩ := hcore j hj
  have hh := hpair N eps lamStar lam P (θ i+d.thetaB-2*Real.pi) (θ j+d.thetaB-2*Real.pi) s
    hN heps hepsr hls hl hl1 hP hPN hui huj hsd
  dsimp only
  change ‖canceledPair (deformedPoint f _ _ _ _ i) (deformedPoint f _ _ _ _ j)
    (selectedContinuedRoot s (deformedPoint f _ _ _ _ i)) (selectedContinuedRoot s (deformedPoint f _ _ _ _ j))‖ ≤ _
  rw [hyi,hyj]
  exact hh.le

end
end IsingBulk.Tail
