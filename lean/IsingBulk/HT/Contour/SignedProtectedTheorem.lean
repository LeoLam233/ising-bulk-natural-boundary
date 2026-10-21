import IsingBulk.HT.Contour.SignedProtectedEnvelope
import IsingBulk.HT.Contour.SignedProtectedDisk

/-! Common actual signed protected disk and complete current envelope. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set Metric
open scoped Topology
set_option maxHeartbeats 1000000

theorem signed_protected_current_disk_and_envelope (σ : ℂ) (hσ : ‖σ‖=1) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∃ c eps₀ K D κ : ℝ, 0<c ∧ 0<eps₀ ∧ 0<K ∧ 0<D ∧ 0<κ ∧
          ∀ (N : ℕ) (eps lamStar lam : ℝ),
            1≤N → 0<eps → eps<eps₀ → 0<lamStar → lamStar≤lam → lam≤1 →
            AnalyticOnNhd ℂ (signedContinuedCurrentSlice σ N (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ lam)
              (closedBall (radialParameter d.theta eps) (c*lamStar/(N:ℝ)^2)) ∧
            ∀ s ∈ closedBall (radialParameter d.theta eps) (c*lamStar/(N:ℝ)^2),
              ‖signedContinuedCurrentSlice σ N (constructedSelector d.thetaB η α)
                (Real.exp (-d.c₀*eps)) τ lam s‖≤
                (K/lam^2)*D^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηE,hηE,hE⟩ := signed_constructed_current_complete_envelope σ hσ d hcsmall
  obtain ⟨ηH,τH,hηH,hτH,hH⟩ := signed_constructed_current_holomorphic_disk σ hσ d hcsmall
  refine ⟨min ηE ηH,lt_min hηE hηH,?_⟩
  intro η hη hηlt
  obtain ⟨αE,τE,hαE,hτE,hsource⟩ := hE η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αE (Real.sin d.thetaB/4),min τE τH,
    lt_min hαE (by positivity [d.a_pos]),lt_min hτE hτH,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨cE,eE,K,D,κ,hcE,heE,hK,hD,hκ,hbound⟩ := hsource α τ hα
    (hαlt.trans_le (min_le_left _ _)) hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cH,eH,hcH,heH,hhol⟩ := hH η α τ hη (hηlt.trans_le (min_le_right _ _)) hα
    (hαlt.trans_le (min_le_right _ _)) hτ (hτlt.trans_le (min_le_right _ _))
  refine ⟨min cE cH,min eE eH,K,D,κ,lt_min hcE hcH,lt_min heE heH,hK,hD,hκ,?_⟩
  intro N eps lamStar lam hN heps hepslt hls hl hl1
  constructor
  · exact (hhol N eps lamStar lam hN heps (hepslt.trans_le (min_le_right _ _)) hls hl hl1).mono
      (closedBall_subset_closedBall (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hls.le) (sq_nonneg (N:ℝ))))
  · intro s hs
    exact hbound N eps lamStar lam s hN heps (hepslt.trans_le (min_le_left _ _)) hls hl hl1
      ((show ‖s-radialParameter d.theta eps‖≤min cE cH*lamStar/(N:ℝ)^2 by
        simpa only [mem_closedBall,dist_eq_norm] using hs).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hls.le) (sq_nonneg (N:ℝ))))

end
end IsingBulk.HT.Contour
