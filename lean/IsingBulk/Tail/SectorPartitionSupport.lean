import IsingBulk.Tail.ConstructedSectorPartition
import IsingBulk.Tail.OriginalPairSupport
import IsingBulk.Analysis.JetsMultiindex

/-! Actual original/current support attachments for the fixed L/R/B labels.
The upper branch is excluded by the literal selector, and every finite real
cutoff jet retains the closed source labels. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Jets Set Function
open scoped Topology BigOperators

theorem cutoffJet_tsupport_subset {N : ℕ} (l : List (Fin N)) (w : (Fin N → ℝ) → ℝ) :
    tsupport (cutoffJet l w) ⊆ tsupport w := by
  induction l with
  | nil => exact Subset.rfl
  | cons i l ih => exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans ih

theorem lowerChord_le_coordinate_square (b theta : ℝ) :
    lowerChord b theta ≤ 2*(theta+b-2*Real.pi)^2 := by
  have hs := Real.abs_sin_sub_sin_le theta (2*Real.pi-b)
  have hc := Real.abs_cos_sub_cos_le theta (2*Real.pi-b)
  rw [Real.sin_two_pi_sub,sub_neg_eq_add,show theta-(2*Real.pi-b)=theta+b-2*Real.pi by ring] at hs
  rw [Real.cos_two_pi_sub,show theta-(2*Real.pi-b)=theta+b-2*Real.pi by ring] at hc
  have hs2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
  simp only [sq_abs] at hs2 hc2
  unfold lowerChord
  linarith

theorem constructed_sector_branch_plateau {b eta : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta,
      delta ≤ delta0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ theta : ℝ, 0 ≤ theta → theta ≤ 2*Real.pi → Real.sin theta ≤ 3*alpha/2 →
      theta ∈ tsupport (sectorBranch b delta hd) →
      (constructedSelector b eta alpha).m theta=1 ∧ (constructedSelector b eta alpha).p theta=0 := by
  obtain ⟨delta0,hd0,hwidth⟩ := sector_branch_support_lower_chart hb hbpi (half_pos heta)
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta alpha halpha halphasmall theta ht0 htpi hsin hsupp
  have hsint : Real.sin theta ≤ Real.sin b/2 := by
    have hbpos := Real.sin_pos_of_pos_of_lt_pi hb hbpi
    linarith
  have hu := hwidth delta hd hdelta theta ht0 htpi hsint hsupp
  have hu2 : (theta+b-2*Real.pi)^2 ≤ (eta/2)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hu.le 2
    simpa only [sq_abs] using hh
  have hc := lowerChord_le_coordinate_square b theta
  apply constructed_lower_core_plateau (Real.sin_pos_of_pos_of_lt_pi hb hbpi) heta hetasmall halpha
  nlinarith

theorem original_sector_branch_lower_chart {b h : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hh : 0 < h) : ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta,
      delta ≤ delta0 → ∀ N : ℕ, ∀ eta alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ theta : Fin N → ℝ, theta ∈ angleBox N →
      theta ∈ tsupport (angularSelector (constructedSelector b eta alpha)) →
      ∀ i : Fin N, theta i ∈ tsupport (sectorBranch b delta hd) → |theta i+b-2*Real.pi| < h := by
  obtain ⟨delta0,hd0,hwidth⟩ := sector_branch_support_lower_chart hb hbpi hh
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta N eta alpha halpha halphasmall theta hbox hsel i hi
  have hs : Real.sin (theta i) ≤ 3*alpha/2 :=
    constructed_original_support_sine_upper b eta alpha halpha i hsel
  exact hwidth delta hd hdelta (theta i) (hbox.1 i) (hbox.2 i)
    (by have := Real.sin_pos_of_pos_of_lt_pi hb hbpi; linarith) hi

theorem current_sector_branch_lower_chart {b h : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hh : 0 < h) : ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta,
      delta ≤ delta0 → ∀ N : ℕ, ∀ eta alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ theta : Fin N → ℝ, theta ∈ angleBox N → ∀ q : Fin N,
      theta ∈ tsupport (namedSelectorDerivative (constructedSelector b eta alpha) q) →
      ∀ i : Fin N, theta i ∈ tsupport (sectorBranch b delta hd) → |theta i+b-2*Real.pi| < h := by
  obtain ⟨delta0,hd0,hwidth⟩ := sector_branch_support_lower_chart hb hbpi hh
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta N eta alpha halpha halphasmall theta hbox q hsel i hi
  have hs : Real.sin (theta i) ≤ 3*alpha/2 :=
    constructed_current_support_sine_upper b eta alpha halpha q i hsel
  exact hwidth delta hd hdelta (theta i) (hbox.1 i) (hbox.2 i)
    (by have := Real.sin_pos_of_pos_of_lt_pi hb hbpi; linarith) hi


theorem current_named_sector_nonbranch {b eta : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (heta : 0 < eta) (hetasmall : eta ≤ Real.sin b/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta,
      delta ≤ delta0 → ∀ alpha : ℝ, 0 < alpha → alpha < Real.sin b/4 →
      ∀ N : ℕ, ∀ q : Fin N, ∀ theta : Fin N → ℝ, theta ∈ angleBox N →
      theta ∈ tsupport (namedSelectorDerivative (constructedSelector b eta alpha) q) →
      theta q ∉ tsupport (sectorBranch b delta hd) := by
  obtain ⟨delta0,hd0,hplateau⟩ := constructed_sector_branch_plateau hb hbpi heta hetasmall
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta alpha halpha halphasmall N q theta hbox hcurrent hB
  have hsine : Real.sin (theta q) ≤ 3*alpha/2 :=
    constructed_current_support_sine_upper b eta alpha halpha q q hcurrent
  have hp0 := (hplateau delta hd hdelta alpha halpha halphasmall (theta q)
    (hbox.1 q) (hbox.2 q) hsine hB).2
  have hf := constructedSelector_regular b eta alpha (Real.sin_pos_of_pos_of_lt_pi hb hbpi)
    heta hetasmall halpha
  have hp1 := (current_named_plateau_tsupport _ hf q hcurrent).1
  rw [hp0] at hp1
  norm_num at hp1

end
end IsingBulk.Tail
