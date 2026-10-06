import IsingBulk.Tail.SectorMicrocoreBridge
import IsingBulk.Tail.SelectedFAsymptotic

/-! Actual W-partition microcore window sums at the FIRST scale. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.PrimeFamily Filter Asymptotics
open scoped Topology

def sectorMicrocoreWindowTerm (d : LocalBranchData) (eta delta : ℝ) (hd : 0 < delta)
    (A c D : ℝ) (j : ℕ) (eps : ℝ) (n : ℕ) : ℝ :=
  if ((n+2:ℕ):ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) then
    ‖iteratedDeriv j (sectorMicrocoreIntegral n d eta delta hd eps (microcoreRadius A c (n+2)))
      (radialParameter d.theta eps)‖ else 0

theorem selected_sector_microcore_window_littleO {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (tau alpha : ℝ) (htau : 0 < tau) (halpha : 0 < alpha)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb tau alpha htau halpha
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧
      ∀ j ≤ J,
        (∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (sectorMicrocoreWindowTerm d eta delta hd A c D j eps)) ∧
        (fun eps : ℝ => ∑' n : ℕ, sectorMicrocoreWindowTerm d eta delta hd A c D j eps n)
          =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  let d := selectedLocalBranchData ha hb tau alpha htau halpha
  obtain ⟨A,c,E,hA,hc,hcs,hcd,hE,hs,hbound⟩ :=
    selected_sector_microcore hp ha hb tau alpha htau halpha eta delta hd hdsmall J D hD
  have hs' : Summable (fun n : ℕ => microcoreMajorant A c E (n+2)) :=
    (summable_nat_add_iff 2).mpr hs
  have hmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0, ∀ j ≤ J, ∀ n : ℕ,
      sectorMicrocoreWindowTerm d eta delta hd A c D j eps n ≤ microcoreMajorant A c E (n+2) := by
    filter_upwards [log_inverse_tendsto_atTop.eventually hbound,self_mem_nhdsWithin] with eps he heps
    intro j hj n
    unfold sectorMicrocoreWindowTerm
    split_ifs with hn
    · have h := he n hn j hj
      have hexp : Real.exp (-Real.log (1/eps))=eps := by
        rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
      simp only [hexp] at h
      simpa only [microcoreMajorant,microcore_sqrt_power_eq_rpow _
        (microcoreRadius_pos A c hc (n+2) (by omega)).le (n+2) (by omega)] using h
    · unfold microcoreMajorant
      positivity
  have hn (j : ℕ) (eps : ℝ) (n : ℕ) :
      0 ≤ sectorMicrocoreWindowTerm d eta delta hd A c D j eps n := by
    unfold sectorMicrocoreWindowTerm
    split_ifs <;> positivity
  refine ⟨A,c,hA,hc,hcs,hcd,?_⟩
  intro j hj
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      Summable (sectorMicrocoreWindowTerm d eta delta hd A c D j eps) := by
    filter_upwards [hmajor] with eps h
    exact Summable.of_nonneg_of_le (hn j eps) (h j hj) hs'
  refine ⟨hsum,?_⟩
  have hO : (fun eps : ℝ => ∑' n : ℕ, sectorMicrocoreWindowTerm d eta delta hd A c D j eps n)
      =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) := by
    apply IsBigO.of_bound (∑' n : ℕ, microcoreMajorant A c E (n+2))
    filter_upwards [hmajor,hsum] with eps h hse
    have ht := Summable.tsum_le_tsum (h j hj) hse hs'
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hn j eps)),norm_one,mul_one] using ht
  have hsmall : (fun _ : ℝ => (1:ℝ)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
    simpa only [zero_mul,Real.exp_zero] using radial_log_square_growth_littleO 0
  exact hO.trans_isLittleO hsmall

end
end IsingBulk.Tail
