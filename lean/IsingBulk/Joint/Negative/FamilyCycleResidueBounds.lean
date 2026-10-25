import IsingBulk.Joint.Negative.FamilyCycleBounds
import IsingBulk.Joint.Negative.FamilyWindingSlope
import IsingBulk.Anisotropic.NegativeCycles.ComplexResidueBound

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_cycle_residue_gaussian (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℂ,
      ∀T : Config (2*m+1)→ℂ, ∀v : Config (2*m+1),
      ‖d‖<r → ‖T v‖<r → (∀i, ‖v i‖<r) →
      ‖poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi d T v‖≤
        2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)) := by
  obtain ⟨a,M,ha,hM,hnum⟩ := compact_family_cycle_numerator_gaussian B rootB phi hphi hQ hB hroot
  obtain ⟨b,c,hb,hc,hslope⟩ := compact_family_pole_derivative_lower B phi hphi hQ hB hBn
  let r := min a (b/2)
  have hr : 0<r := lt_min ha (half_pos hb)
  have hra : r≤a := min_le_left _ _
  have hrb : r≤b/2 := min_le_right _ _
  refine ⟨r,M,c,hr,hM,hc,?_⟩
  intro eta heta m d T v hd ht hv
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  have hN := hnum eta heta m d (T v) v (hd.trans_le hra) (ht.trans_le hra) (fun i => (hv i).trans_le hra)
  have hD := hslope eta heta (2*m+1) (by omega) d (T v) v (by linarith)
    (fun i => lt_of_le_of_lt (norm_add_le d (v i)) (by linarith [hv i]))
  unfold poleResidue
  rw [norm_div,norm_mul,norm_neg]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hN (by norm_num))
    (by positivity) hD


end
end IsingBulk.Joint.Negative
