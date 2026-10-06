import IsingBulk.Tail.SectorMicrocoreAsymptotic
import IsingBulk.Tail.SectorMicrocoreAngleBox
import IsingBulk.Tail.RadialSourceDomain

/-! Literal angleBox microcore absolute window sum at the FIRST scale. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.PrimeFamily Filter Asymptotics
open scoped Topology

def angleBoxMicrocoreWindowTerm (d : LocalBranchData) (eta delta : ℝ) (hd : 0 < delta)
    (A c D : ℝ) (j : ℕ) (eps : ℝ) (n : ℕ) : ℝ :=
  if ((n+2:ℕ):ℝ) ≤ D*Real.sqrt (Real.log (1/eps)) then
    ‖iteratedDeriv j (angleBoxMicrocoreIntegral n d eta delta hd eps (microcoreRadius A c (n+2)))
      (radialParameter d.theta eps)‖ else 0

theorem selected_angleBox_microcore_window_littleO {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (tau alpha : ℝ) (htau : 0 < tau) (halpha : 0 < alpha)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2)
    (hdb : delta ≤ branchAngle p a b) (hdpi : delta ≤ Real.pi-branchAngle p a b)
    (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb tau alpha htau halpha
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧
      ∀ j ≤ J,
        (∀ᶠ eps : ℝ in 𝓝[>] 0, Summable (angleBoxMicrocoreWindowTerm d eta delta hd A c D j eps)) ∧
        (fun eps : ℝ => ∑' n : ℕ, angleBoxMicrocoreWindowTerm d eta delta hd A c D j eps n)
          =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  let d := selectedLocalBranchData ha hb tau alpha htau halpha
  obtain ⟨A,c,hA,hc,hcs,hcd,hmain⟩ :=
    selected_sector_microcore_window_littleO hp ha hb tau alpha htau halpha eta delta hd hdsmall J D hD
  refine ⟨A,c,hA,hc,hcs,hcd,?_⟩
  intro j hj
  obtain ⟨hsum,hsmall⟩ := hmain j hj
  have heq : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      angleBoxMicrocoreWindowTerm d eta delta hd A c D j eps = sectorMicrocoreWindowTerm d eta delta hd A c D j eps := by
    filter_upwards [radial_source_eventually_damping d (selectedLocalBranchData_c0_small ha hb tau alpha htau halpha),
      self_mem_nhdsWithin] with eps hdom heps
    funext n
    unfold angleBoxMicrocoreWindowTerm sectorMicrocoreWindowTerm
    split_ifs
    · have hn : 0 < microcoreRadius A c (n+2) := microcoreRadius_pos A c hc (n+2) (by omega)
      have hnc := microcoreRadius_le_prefactor A c hA.le hc.le (n+2) (by omega)
      have hnd := hnc.trans hcd
      have hnb : microcoreRadius A c (n+2) ≤ d.thetaB/2 := by
        change microcoreRadius A c (n+2) ≤ branchAngle p a b/2
        linarith
      have hnpi : microcoreRadius A c (n+2) ≤ (Real.pi-d.thetaB)/2 := by
        change microcoreRadius A c (n+2) ≤ (Real.pi-branchAngle p a b)/2
        linarith
      rw [angleBoxMicrocoreIntegral_iteratedDeriv_eq n d eta delta eps _ hd hdsmall heps hn hnd hnb hnpi _ hdom.2.2 j]
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
end IsingBulk.Tail
