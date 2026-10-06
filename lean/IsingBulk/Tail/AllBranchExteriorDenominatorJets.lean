import IsingBulk.Tail.AllBranchExteriorWeights
import IsingBulk.Tail.AllBranchExteriorInverseJets
import IsingBulk.Tail.CoordinateDifferenceJets

/-! Dimension-explicit actual denominator jets for the source rational
weights. No derivative bound is supplied as a certificate premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped BigOperators ContDiff

theorem allBranchExterior_linear_power_scaled {N : ℕ} (p q : Fin N) (m J : ℕ)
    (hm : 1 ≤ m) (hJ : J ≤ m) (u : Fin N → ℝ) (d : ℝ) (_hd : 0 < d)
    (hu : |u p-u q| ≤ d) :
    AllBranchExteriorScaledJets (fun x => (x p-x q)^m) u J d ((m:ℝ)^J) (m:ℤ) := by
  refine ⟨by positivity,?_⟩
  intro l hl
  have hlen : l.length ≤ m := hl.trans hJ
  have hc : (m.descFactorial l.length:ℝ) ≤ (m:ℝ)^J := by
    have hh := (Nat.descFactorial_le_pow m l.length).trans (Nat.pow_le_pow_right hm hl)
    exact_mod_cast hh
  have hn := coordinate_difference_jet_norm p q m l u
  rw [Real.norm_eq_abs] at hn
  have hpow : |u p-u q|^(m-l.length) ≤ d^(m-l.length) := pow_le_pow_left₀ (abs_nonneg _) hu _
  have he : (m:ℤ)-(l.length:ℤ)=((m-l.length:ℕ):ℤ) := by omega
  rw [he,zpow_natCast]
  exact hn.trans (mul_le_mul hc hpow (pow_nonneg (abs_nonneg _) _) (by positivity))

theorem allBranchExteriorWeightDenom_smooth {N : ℕ} (M : ℕ) :
    ContDiff ℝ ∞ (allBranchExteriorWeightDenom (N := N) M) := by
  unfold allBranchExteriorWeightDenom
  fun_prop

theorem allBranchExterior_denominator_scaled {N : ℕ} (M J : ℕ) (hM : 0 < M)
    (hJ : J ≤ 2*M) (u : Fin N → ℝ) (hu : 0 < allBranchExteriorDiameter u) :
    AllBranchExteriorScaledJets (allBranchExteriorWeightDenom M) u J
      (allBranchExteriorDiameter u) ((N:ℝ)^2*(2*M:ℕ)^J) (2*M:ℕ) := by
  refine ⟨by positivity,?_⟩
  intro l hl
  unfold allBranchExteriorWeightDenom
  rw [cutoffJet_finset_sum _ l _ isOpen_univ
    (fun p _ x _ => (show ContDiff ℝ ∞ (fun y : Fin N → ℝ => (y p.1-y p.2)^(2*M)) by fun_prop).contDiffAt)
    u (mem_univ u)]
  apply (norm_sum_le _ _).trans
  have hp : ∀ p : Fin N × Fin N,
      ‖cutoffJet l (fun x => (x p.1-x p.2)^(2*M)) u‖ ≤
        (2*M:ℕ)^J*(allBranchExteriorDiameter u)^((2*M:ℕ)-(l.length:ℤ)) := by
    intro p
    exact (allBranchExterior_linear_power_scaled p.1 p.2 (2*M) J (by omega) hJ u _ hu
      (allBranchExterior_pair_le_diameter u p.1 p.2)).bound l hl
  have hcard : (orderedIndexPairs (Finset.univ : Finset (Fin N))).card ≤ N^2 := by
    apply (Finset.card_filter_le _ _).trans_eq
    simp [pow_two]
  have hcardR : ((orderedIndexPairs (Finset.univ : Finset (Fin N))).card:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hcard
  calc
    _ ≤ ∑ _p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
        (2*M:ℕ)^J*(allBranchExteriorDiameter u)^((2*M:ℕ)-(l.length:ℤ)) :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = ((orderedIndexPairs (Finset.univ : Finset (Fin N))).card:ℝ)*
        ((2*M:ℕ)^J*(allBranchExteriorDiameter u)^((2*M:ℕ)-(l.length:ℤ))) := by simp
    _ ≤ (N:ℝ)^2*((2*M:ℕ)^J*(allBranchExteriorDiameter u)^((2*M:ℕ)-(l.length:ℤ))) := by gcongr
    _ = _ := by push_cast; ring

theorem allBranchExterior_denominator_inverse_scaled {N : ℕ} (M J : ℕ) (hM : 0 < M)
    (hJ : J ≤ 2*M) (u : Fin N → ℝ) (hu : 0 < allBranchExteriorDiameter u) :
    AllBranchExteriorScaledJets (fun x => (allBranchExteriorWeightDenom M x)⁻¹) u J
      (allBranchExteriorDiameter u)
      (allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J) (-(2*M:ℕ)) := by
  let U := {x : Fin N → ℝ | allBranchExteriorWeightDenom M x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (allBranchExteriorWeightDenom_smooth M).continuous continuous_const
  apply allBranchExterior_scaled_inverse (allBranchExteriorWeightDenom M) hU
    (fun x _ => (allBranchExteriorWeightDenom_smooth M).contDiffAt) (fun _ hx => hx) u
    (allBranchExterior_weightDenom_pos M u hu).ne' J _ _ hu (2*M:ℕ)
    (allBranchExterior_denominator_scaled M J hM hJ u hu)
  simpa only [zpow_natCast] using allBranchExterior_weightDenom_diameter_lower M u hu

end
end IsingBulk.Tail
