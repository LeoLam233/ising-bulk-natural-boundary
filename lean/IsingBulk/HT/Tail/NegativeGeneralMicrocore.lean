import IsingBulk.HT.Tail.NegativeAngleBoxMicrocoreAsymptotic
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.PrimeFamily IsingBulk.Tail Filter Asymptotics
open scoped Topology
theorem negative_nonresonant_sector_microcore (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ,1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let eps := Real.exp (-H)
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (negativeSectorMicrocoreIntegral n d eta delta hd eps bN) (radialParameter d.theta eps)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let cap := min (delta/2) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2))
  have hcap : 0 < cap := by
    have h1 := d.thetaB_pos
    have h2 : 0 < Real.pi-d.thetaB := sub_pos.mpr d.thetaB_lt
    dsimp [cap]
    positivity
  obtain ⟨A,c,E,hA,hc,hcs,hcCap,hE,hSum,hbound⟩ :=
    negative_nonresonant_microcore d halg hnot cap hcap J D hD
  refine ⟨A,c,E,hA,hc,hcs,hcCap.trans (min_le_left _ _),hE,hSum,?_⟩
  filter_upwards [hbound] with H hH
  intro n hwindow
  dsimp only
  intro j hj
  have hbN := microcoreRadius_pos A c hc (n+2) (by omega)
  have hbc := microcoreRadius_le_prefactor A c hA.le hc.le (n+2) (by omega)
  have hdeltaN := hbc.trans (hcCap.trans (min_le_left _ _))
  have hbN' := hbc.trans (hcCap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpiN := hbc.trans (hcCap.trans ((min_le_right _ _).trans (min_le_right _ _)))
  rw [negative_sectorMicrocoreIntegral_eq n d eta delta _ _ hd hdsmall hbN hdeltaN hbN' hpiN]
  exact hH n hwindow j hj

theorem negative_nonresonant_sector_microcore_window_littleO (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ,1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧
      ∀ j ≤ J,
        (∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps)) ∧
        (fun eps : ℝ => ∑' n : ℕ, negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps n)
          =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨A,c,E,hA,hc,hcs,hcd,hE,hs,hbound⟩ :=
    negative_nonresonant_sector_microcore d halg hnot eta delta hd hdsmall J D hD
  have hs' : Summable (fun n : ℕ => microcoreMajorant A c E (n+2)) :=
    (summable_nat_add_iff 2).mpr hs
  have hmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0, ∀ j ≤ J, ∀ n : ℕ,
      negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps n ≤ microcoreMajorant A c E (n+2) := by
    filter_upwards [log_inverse_tendsto_atTop.eventually hbound,self_mem_nhdsWithin] with eps he heps
    intro j hj n
    unfold negativeSectorMicrocoreWindowTerm
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
      0 ≤ negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps n := by
    unfold negativeSectorMicrocoreWindowTerm
    split_ifs <;> positivity
  refine ⟨A,c,hA,hc,hcs,hcd,?_⟩
  intro j hj
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      Summable (negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps) := by
    filter_upwards [hmajor] with eps h
    exact Summable.of_nonneg_of_le (hn j eps) (h j hj) hs'
  refine ⟨hsum,?_⟩
  have hO : (fun eps : ℝ => ∑' n : ℕ, negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps n)
      =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) := by
    apply IsBigO.of_bound (∑' n : ℕ, microcoreMajorant A c E (n+2))
    filter_upwards [hmajor,hsum] with eps h hse
    have ht := Summable.tsum_le_tsum (h j hj) hse hs'
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hn j eps)),norm_one,mul_one] using ht
  have hsmall : (fun _ : ℝ => (1:ℝ)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
    simpa only [zero_mul,Real.exp_zero] using radial_log_square_growth_littleO 0
  exact hO.trans_isLittleO hsmall

theorem negative_nonresonant_angleBox_microcore_window_littleO (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ,1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (hcsmall : d.c₀ < Real.sin d.theta/2)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2)
    (hdb : delta ≤ d.thetaB) (hdpi : delta ≤ Real.pi-d.thetaB)
    (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧
      ∀ j ≤ J,
        (∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (negativeAngleBoxMicrocoreWindowTerm d eta delta hd A c D j eps)) ∧
        (fun eps : ℝ => ∑' n : ℕ, negativeAngleBoxMicrocoreWindowTerm d eta delta hd A c D j eps n)
          =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨A,c,hA,hc,hcs,hcd,hmain⟩ :=
    negative_nonresonant_sector_microcore_window_littleO d halg hnot eta delta hd hdsmall J D hD
  refine ⟨A,c,hA,hc,hcs,hcd,?_⟩
  intro j hj
  obtain ⟨hsum,hsmall⟩ := hmain j hj
  have heq : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      negativeAngleBoxMicrocoreWindowTerm d eta delta hd A c D j eps = negativeSectorMicrocoreWindowTerm d eta delta hd A c D j eps := by
    filter_upwards [radial_source_eventually_damping d hcsmall,
      self_mem_nhdsWithin] with eps hdom heps
    funext n
    unfold negativeAngleBoxMicrocoreWindowTerm negativeSectorMicrocoreWindowTerm
    split_ifs
    · have hn : 0 < microcoreRadius A c (n+2) := microcoreRadius_pos A c hc (n+2) (by omega)
      have hnc := microcoreRadius_le_prefactor A c hA.le hc.le (n+2) (by omega)
      have hnd := hnc.trans hcd
      have hnb : microcoreRadius A c (n+2) ≤ d.thetaB/2 := by
        linarith
      have hnpi : microcoreRadius A c (n+2) ≤ (Real.pi-d.thetaB)/2 := by
        linarith
      rw [negative_angleBoxMicrocoreIntegral_iteratedDeriv_eq n d eta delta eps _ hd hdsmall heps hn hnd hnb hnpi _ hdom.2.2 j]
    · rfl
  constructor
  · filter_upwards [heq,hsum] with eps he hs
    rw [he]
    exact hs
  · apply hsmall.congr'
    · filter_upwards [heq] with eps he
      exact congrArg (fun f : ℕ → ℝ => ∑' n, f n) he.symm
    · exact Filter.Eventually.of_forall (fun _ => rfl)

end
end IsingBulk.HT.Tail
