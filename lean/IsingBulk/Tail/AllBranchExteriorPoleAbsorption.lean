import IsingBulk.Tail.AllBranchExteriorWeightJets
import IsingBulk.Tail.AllBranchExteriorPhaseSeparation

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets

/-- Cancelling a selected-pair pole costs exactly its order plus the cutoff
word length in the diameter. No repeated inverse recurrence changes this exponent. -/
theorem allBranchExterior_scalar_pole_absorption (δ d z c : ℝ) (P l m : ℕ)
    (hδ : 0 < δ) (hd : δ ≤ d) (hc : 0 < c) (hz : c*δ ≤ z) (hm : m ≤ P) :
    (δ^P/d^(P+l))/z^m ≤ (c⁻¹)^m/(d^(l+m)) := by
  have hdp : 0 < d := hδ.trans_le hd
  have hzp : 0 < z := (mul_pos hc hδ).trans_le hz
  have h₁ : (δ^P/d^(P+l))/z^m ≤ (δ^P/d^(P+l))/(c*δ)^m := by
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos hc hδ) _)
      (pow_le_pow_left₀ (by positivity) hz _)
  have h₂ : δ^(P-m) ≤ d^(P-m) := pow_le_pow_left₀ hδ.le hd _
  have he : P = (P-m)+m := by omega
  calc
    _ ≤ (δ^P/d^(P+l))/(c*δ)^m := h₁
    _ = (δ^(P-m)/d^(P+l))*(c⁻¹)^m := by
      conv_lhs => rw [he,pow_add,mul_pow]
      rw [inv_pow]
      field_simp
      congr 1
      omega
    _ ≤ (d^(P-m)/d^(P+l))*(c⁻¹)^m := by gcongr
    _ = (c⁻¹)^m/d^(l+m) := by
      have hpow : d^(P+l)=d^(P-m)*d^(l+m) := by rw [← pow_add]; congr 1; omega
      rw [hpow]
      field_simp

theorem allBranchExterior_actual_pole_absorption (d₀ : LocalBranchData)
    (M J : ℕ) (hM : 0 < M) (hJ : J < 2*M) :
    ∃ C : ℕ, 0 < C ∧ ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N →
      ∀ p q : Fin N, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) → u p ≠ u q →
      ∀ l : List (Fin N), l.length ≤ J → ∀ m : ℕ, m+l.length ≤ 2*M →
      ‖cutoffJet l (allBranchExteriorPairWeight M p q) u‖ /
        ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m ≤
      ((C:ℝ)*(N:ℝ)^C)*(c⁻¹)^m/(allBranchExteriorDiameter u)^(l.length+m) := by
  obtain ⟨C,hC,hweight⟩ := allBranchExterior_weight_jets_uniform M J hM hJ
  obtain ⟨c,r,hc,hr,hsep⟩ := original_phase_difference_lower d₀
  refine ⟨C,hC,c,r,hc,hr,?_⟩
  intro ε hε hεr N hN p q u hu hpq l hl m hm
  have hδ : 0 < |u p-u q| := abs_pos.mpr (sub_ne_zero.mpr hpq)
  have hdiam := allBranchExterior_pair_le_diameter u p q
  have hd := hδ.trans_le hdiam
  have hw := hweight N hN p q u hd l hl
  have hz := hsep ε (u p) (u q) hε hεr (hu p) (hu q)
  have hs := allBranchExterior_scalar_pole_absorption |u p-u q|
    (allBranchExteriorDiameter u) ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖
    c (2*M-l.length) l.length m hδ hdiam hc hz (by omega)
  have he : 2*M-l.length+l.length=2*M := by omega
  rw [he] at hs
  calc
    _ ≤ (((C:ℝ)*(N:ℝ)^C)*|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M))/
        ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m :=
      div_le_div_of_nonneg_right hw (by positivity)
    _ = ((C:ℝ)*(N:ℝ)^C)*((|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M))/
        ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m) := by ring
    _ ≤ ((C:ℝ)*(N:ℝ)^C)*((c⁻¹)^m/(allBranchExteriorDiameter u)^(l.length+m)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end
end IsingBulk.Tail
