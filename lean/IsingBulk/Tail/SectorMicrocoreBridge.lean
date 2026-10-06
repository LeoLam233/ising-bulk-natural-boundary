import IsingBulk.Tail.SectorAssignmentPartition
import IsingBulk.Tail.MicrocoreSourceCutoffs

/-! The new fixed W-based B label and the original periodic branch label
both equal one on the capped microcore. The established microcore estimate
therefore attaches to the exact newly constructed finite partition. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First IsingBulk.PrimeFamily MeasureTheory Filter
open scoped BigOperators Topology

theorem sector_microcore_weight_identity {N : ℕ} (b delta alpha eta r : ℝ)
    (hb : 0 < b) (hbpi : b < Real.pi) (hd : 0 < delta) (hdsmall : delta ≤ 1/2)
    (halpha : 0 < alpha) (hr : 0 < r) (hrd : r ≤ delta/2)
    (hrb : r ≤ b/2) (hrpi : r ≤ (Real.pi-b)/2) (u : Fin N → ℝ) :
    scaledMicroCutoff N r u*angularSelector (constructedSelector b eta alpha) (fun i => u i-b)*
      sectorAssignmentWeight b delta hd (fun _ : Fin N => (2:Fin 3)) (fun i => u i-b)=
      scaledMicroCutoff N r u := by
  by_cases hz : scaledMicroCutoff N r u=0
  · simp [hz]
  · have hu := scaledMicroCutoff_jet_tsupport hr [] (subset_closure hz)
    have hpsi := (microcore_selector_branch_plateau b delta alpha eta r hb hbpi hd hdsmall
      halpha hrd hrb hrpi u hu).1
    have hB : sectorAssignmentWeight b delta hd (fun _ : Fin N => (2:Fin 3)) (fun i => u i-b)=1 := by
      simpa only [sub_eq_add_neg,add_comm] using
        sector_all_branch_micro_plateau b delta hd u (fun i => (hu i).trans hrd)
    rw [hpsi,hB,mul_one,mul_one]

def sectorMicrocoreIntegral (n : ℕ) (d : LocalBranchData) (eta delta : ℝ) (hd : 0 < delta)
    (eps r : ℝ) (s : ℂ) : ℂ :=
  ((n+2).factorial:ℂ)⁻¹*∫ u : Fin (n+2) → ℝ,
    (scaledMicroCutoff (n+2) r u*angularSelector (constructedSelector d.thetaB eta d.alpha)
      (fun i => u i-d.thetaB)*sectorAssignmentWeight d.thetaB delta hd
        (fun _ : Fin (n+2) => (2:Fin 3)) (fun i => u i-d.thetaB):ℝ)*
      sourceReducedAngularDensity (Real.exp (-d.c₀*eps)) s (fun i => u i-d.thetaB)

theorem sectorMicrocoreIntegral_eq (n : ℕ) (d : LocalBranchData) (eta delta eps r : ℝ)
    (hd : 0 < delta) (hdsmall : delta ≤ 1/2) (hr : 0 < r)
    (hrd : r ≤ delta/2) (hrb : r ≤ d.thetaB/2) (hrpi : r ≤ (Real.pi-d.thetaB)/2) :
    sectorMicrocoreIntegral n d eta delta hd eps r=originalMicrocoreIntegral n d eps r := by
  funext s
  unfold sectorMicrocoreIntegral originalMicrocoreIntegral
  simp_rw [sector_microcore_weight_identity d.thetaB delta d.alpha eta r d.thetaB_pos d.thetaB_lt
    hd hdsmall d.alpha_pos hr hrd hrb hrpi]

theorem selected_sector_microcore {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (tau alpha : ℝ) (htau : 0 < tau) (halpha : 0 < alpha)
    (eta delta : ℝ) (hd : 0 < delta) (hdsmall : delta ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb tau alpha htau halpha
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ delta/2 ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let eps := Real.exp (-H)
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (sectorMicrocoreIntegral n d eta delta hd eps bN) (radialParameter d.theta eps)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let d := selectedLocalBranchData ha hb tau alpha htau halpha
  let cap := min (delta/2) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2))
  have hcap : 0 < cap := by
    have h1 := d.thetaB_pos
    have h2 : 0 < Real.pi-d.thetaB := sub_pos.mpr d.thetaB_lt
    dsimp [cap]
    positivity
  obtain ⟨A,c,E,hA,hc,hcs,hcCap,hE,hSum,hbound⟩ :=
    selected_nonresonant_microcore hp ha hb tau alpha htau halpha cap hcap J D hD
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
  rw [sectorMicrocoreIntegral_eq n d eta delta _ _ hd hdsmall hbN hdeltaN hbN' hpiN]
  exact hH n hwindow j hj

end
end IsingBulk.Tail
