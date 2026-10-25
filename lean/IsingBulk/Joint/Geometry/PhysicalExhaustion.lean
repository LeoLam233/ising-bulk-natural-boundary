import IsingBulk.Joint.Geometry.Exhaustion

namespace IsingBulk.Joint
noncomputable section
open Set Metric Real

theorem IsPlurisubharmonicOn.add {φ ψ : Coupling → ℝ} {D : Set Coupling}
    (hφ : IsPlurisubharmonicOn φ D) (hψ : IsPlurisubharmonicOn ψ D) :
    IsPlurisubharmonicOn (fun K => φ K + ψ K) D := by
  refine ⟨hφ.1.add hψ.1,?_⟩
  intro K V R hD
  have hiφ : CircleIntegrable (fun z : ℂ => φ (K+z•V)) 0 R :=
    (hφ.1.comp (by fun_prop) (fun z hz => hD z (sphere_subset_closedBall hz))).circleIntegrable'
  have hiψ : CircleIntegrable (fun z : ℂ => ψ (K+z•V)) 0 R :=
    (hψ.1.comp (by fun_prop) (fun z hz => hD z (sphere_subset_closedBall hz))).circleIntegrable'
  rw [circleAverage_fun_add hiφ hiψ]
  exact add_le_add (hφ.2 K V R hD) (hψ.2 K V R hD)

theorem IsPlurisubharmonicOn.nonneg_mul {φ : Coupling → ℝ} {D : Set Coupling}
    (hφ : IsPlurisubharmonicOn φ D) {c : ℝ} (hc : 0 ≤ c) :
    IsPlurisubharmonicOn (fun K => c*φ K) D := by
  refine ⟨continuousOn_const.mul hφ.1,?_⟩
  intro K V R hD
  have he := circleAverage_fun_smul (f := fun z : ℂ => φ (K+z•V)) (c := (0 : ℂ)) (R := R) (a := c)
  simp only [smul_eq_mul] at he
  rw [he]
  exact mul_le_mul_of_nonneg_left (hφ.2 K V R hD) hc

theorem spectralBarrier_isPlurisubharmonic : IsPlurisubharmonicOn spectralBarrier spectralSetᶜ :=
  ⟨spectralBarrier_continuousOn,spectralBarrier_submean⟩

/-- Literal JOINT Proposition 2.18: Coupling stores z = 2 Kx, w = 2 Ky,
so the physical quadratic term is (|z|² + |w|²)/4. -/
def paperSpectralExhaustion (K : Coupling) : ℝ :=
  (‖K.1‖^2+‖K.2‖^2)/4 + spectralBarrier K

theorem paperSpectralExhaustion_isPlurisubharmonic :
    IsPlurisubharmonicOn paperSpectralExhaustion spectralSetᶜ := by
  have h := (spectralExhaustion_isPlurisubharmonic.nonneg_mul (c := 1/4) (by norm_num)).add
    (spectralBarrier_isPlurisubharmonic.nonneg_mul (c := 3/4) (by norm_num))
  convert h using 1
  funext K
  unfold paperSpectralExhaustion spectralExhaustion
  ring

theorem paperSpectralExhaustion_dominates {K : Coupling} {r : ℝ}
    (hr : paperSpectralExhaustion K ≤ r) : spectralExhaustion K ≤ 4*r := by
  have hb : 0 ≤ spectralBarrier K := le_max_left _ _
  dsimp [paperSpectralExhaustion] at hr
  dsimp [spectralExhaustion]
  linarith

theorem paperSpectralExhaustion_sublevel_isCompact (r : ℝ) :
    IsCompact {K | K ∉ spectralSet ∧ paperSpectralExhaustion K ≤ r} := by
  let C : Set Coupling := {K | K ∉ spectralSet ∧ spectralExhaustion K ≤ 4*r}
  have hc : IsCompact C := spectralExhaustion_sublevel_isCompact (4*r)
  have hh : IsClosed {K | K ∈ C ∧ paperSpectralExhaustion K ≤ r} :=
    hc.isClosed.isClosed_le
      (paperSpectralExhaustion_isPlurisubharmonic.1.mono (fun _ h => h.1)) continuousOn_const
  have he : {K | K ∉ spectralSet ∧ paperSpectralExhaustion K ≤ r} =
      {K | K ∈ C ∧ paperSpectralExhaustion K ≤ r} := by
    ext K
    exact ⟨fun h => ⟨⟨h.1,paperSpectralExhaustion_dominates h.2⟩,h.2⟩,
      fun h => ⟨h.1.1,h.2⟩⟩
  rw [he]
  exact hc.of_isClosed_subset hh (fun _ h => h.1)

theorem paperSpectralExhaustion_component_sublevel_isCompact {D : Set Coupling}
    (ho : IsOpen D) (hs : D ⊆ spectralSetᶜ) (hb : frontier D ⊆ spectralSet) (r : ℝ) :
    IsCompact {K | K ∈ D ∧ paperSpectralExhaustion K ≤ r} := by
  have he : {K | K ∈ D ∧ paperSpectralExhaustion K ≤ r} =
      closure D ∩ {K | K ∉ spectralSet ∧ paperSpectralExhaustion K ≤ r} := by
    ext K
    constructor
    · rintro ⟨hK,hr⟩
      exact ⟨subset_closure hK,hs hK,hr⟩
    · rintro ⟨hcl,hsp,hr⟩
      refine ⟨?_,hr⟩
      by_contra hn
      exact hsp (hb (by rw [ho.frontier_eq]; exact ⟨hcl,hn⟩))
  rw [he,inter_comm]
  exact (paperSpectralExhaustion_sublevel_isCompact r).inter_right isClosed_closure

theorem physical_components_paper_exhaustion {D : Set Coupling}
    (hD : D = highDomain ∨ D = lowDomain) :
    IsPlurisubharmonicOn paperSpectralExhaustion D ∧
      ∀ r : ℝ, IsCompact {K | K ∈ D ∧ paperSpectralExhaustion K ≤ r} := by
  have hs : D ⊆ spectralSetᶜ := by rcases hD with rfl | rfl; exact highDomain_subset_spectralComplement; exact lowDomain_subset_spectralComplement
  have ho : IsOpen D := by rcases hD with rfl | rfl; exact highDomain_isOpen; exact lowDomain_isOpen
  have hb : frontier D ⊆ spectralSet := by rcases hD with rfl | rfl; exact frontier_high_subset_spectralSet; exact frontier_low_subset_spectralSet
  refine ⟨⟨paperSpectralExhaustion_isPlurisubharmonic.1.mono hs,?_⟩,
    paperSpectralExhaustion_component_sublevel_isCompact ho hs hb⟩
  intro K V R h
  exact paperSpectralExhaustion_isPlurisubharmonic.2 K V R (fun z hz => hs (h z hz))

end
end IsingBulk.Joint
