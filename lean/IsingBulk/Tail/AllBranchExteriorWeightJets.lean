import IsingBulk.Tail.AllBranchExteriorDenominatorJets
import IsingBulk.Tail.QuadraticJetRecurrenceBound

/-! Quantitative literal rational-weight jets retain their selected-pair
zero. The denominator is the actual sum of all even coordinate differences. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped BigOperators ContDiff

theorem allBranchExterior_inverse_jet_polynomial (M J N : ℕ) (hM : 0 < M) (hN : 1 ≤ N) :
    allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J ≤
      (2*(4:ℝ)^J*(2*M:ℕ)^J)^(2^J-1)*(N:ℝ)^(2*(2^J-1)) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (1:ℝ) ≤ (2*M:ℕ) := by exact_mod_cast (show 1 ≤ 2*M by omega)
  have hB : 1 ≤ (N:ℝ)^2*(2*M:ℕ)^J := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hNr) (one_le_pow₀ hMr)
  have hh := quadratic_jet_recurrence_bound
    (allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J)) hB rfl (fun _ => rfl) J J le_rfl
  apply hh.trans_eq
  have he : 2*(4:ℝ)^J*((N:ℝ)^2*(2*M:ℕ)^J)=(2*(4:ℝ)^J*(2*M:ℕ)^J)*(N:ℝ)^2 := by ring
  rw [he,mul_pow,← pow_mul]

theorem allBranchExterior_weight_jet_raw {N : ℕ} (M J : ℕ) (hM : 0 < M) (hJ : J < 2*M)
    (p q : Fin N) (u : Fin N → ℝ) (hu : 0 < allBranchExteriorDiameter u)
    (l : List (Fin N)) (hl : l.length ≤ J) :
    ‖cutoffJet l (allBranchExteriorPairWeight M p q) u‖ ≤
      (2:ℝ)^J*(2*M:ℕ)^J*allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J*
        |u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M) := by
  let d := allBranchExteriorDiameter u
  let C := allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J
  let F : (Fin N → ℝ) → ℝ := fun x => (x p-x q)^(2*M)
  let R : (Fin N → ℝ) → ℝ := fun x => (allBranchExteriorWeightDenom M x)⁻¹
  let U := {x : Fin N → ℝ | allBranchExteriorWeightDenom M x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (allBranchExteriorWeightDenom_smooth M).continuous continuous_const
  have huU : u ∈ U := (allBranchExterior_weightDenom_pos M u hu).ne'
  have hFs : ∀ x ∈ U, ContDiffAt ℝ ∞ F x := fun x _ => (show ContDiff ℝ ∞ F by dsimp [F]; fun_prop).contDiffAt
  have hRs : ∀ x ∈ U, ContDiffAt ℝ ∞ R x := fun x hx => (allBranchExteriorWeightDenom_smooth M).contDiffAt.inv hx
  have he : allBranchExteriorPairWeight M p q=fun x => F x*R x := by
    funext x
    exact div_eq_mul_inv _ _
  have hInv := allBranchExterior_denominator_inverse_scaled M J hM hJ.le u hu
  have hC : 0 ≤ C := hInv.nonneg
  by_cases hδ : u p-u q=0
  · rw [he,cutoffJet_product_word l F R hU hFs hRs u huU]
    have hz : ∀ a ∈ cutoffWordSplits l, cutoffJet a.1 F u=0 := by
      intro a ha
      have hlen := cutoffWordSplits_orders l a ha
      have hp : 0 < 2*M-a.1.length := by omega
      dsimp [F]
      rw [cutoffJet_coordinate_difference_pow,hδ,zero_pow (by omega),mul_zero]
    have hsum : ((cutoffWordSplits l).map (fun a => cutoffJet a.1 F u*cutoffJet a.2 R u)).sum=0 := by
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
      rw [hz a ha,zero_mul]
    rw [hsum,norm_zero,hδ,abs_zero,zero_pow (by omega),mul_zero,zero_div]
  · let δ := |u p-u q|
    have hδp : 0 < δ := abs_pos.mpr hδ
    have hδd : δ ≤ d := allBranchExterior_pair_le_diameter u p q
    have hInvδ : AllBranchExteriorScaledJets R u J δ (C*d^(-((2*M:ℕ):ℤ))) 0 := by
      refine ⟨mul_nonneg hC (zpow_nonneg hu.le _),?_⟩
      intro k hk
      have hh := hInv.bound k hk
      have hp : d^(-(k.length:ℤ)) ≤ δ^(-(k.length:ℤ)) := by
        rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast]
        exact inv_anti₀ (pow_pos hδp _) (pow_le_pow_left₀ hδp.le hδd _)
      have he' : (-((2*M:ℕ):ℤ))-(k.length:ℤ)=(-((2*M:ℕ):ℤ))+(-(k.length:ℤ)) := by ring
      rw [he',zpow_add₀ hu.ne'] at hh
      calc
        _ ≤ C*(d^(-((2*M:ℕ):ℤ))*d^(-(k.length:ℤ))) := hh
        _ ≤ C*(d^(-((2*M:ℕ):ℤ))*δ^(-(k.length:ℤ))) := by gcongr
        _ = _ := by simp only [zero_sub]; ring
    have hNum := allBranchExterior_linear_power_scaled p q (2*M) J (by omega) hJ.le u δ hδp le_rfl
    have hh := (allBranchExterior_scaled_product F R hU hFs hRs u huU J δ ((2*M:ℕ)^J)
      (C*d^(-((2*M:ℕ):ℤ))) hδp (2*M:ℕ) 0 hNum hInvδ).bound l hl
    rw [← he] at hh
    have he' : (2*M:ℕ)+(0:ℤ)-(l.length:ℤ)=((2*M-l.length:ℕ):ℤ) := by omega
    rw [he',zpow_natCast] at hh
    apply hh.trans_eq
    rw [zpow_neg,zpow_natCast]
    dsimp [C,d,δ]
    ring

/-- Appendix D weight-jet estimate, with one constant chosen before N and
all selected pairs. The selected zero and the diameter denominator remain explicit. -/
theorem allBranchExterior_weight_jets_uniform (M J : ℕ) (hM : 0 < M) (hJ : J < 2*M) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ p q : Fin N, ∀ u : Fin N → ℝ,
      0 < allBranchExteriorDiameter u → ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (allBranchExteriorPairWeight M p q) u‖ ≤
        (C:ℝ)*(N:ℝ)^C*|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M) := by
  let P := 2*(2^J-1)
  let A : ℝ := 2^J*(2*M:ℕ)^J*(2*(4:ℝ)^J*(2*M:ℕ)^J)^(2^J-1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨K,hK⟩ := exists_nat_gt A
  let C := K+P+1
  have hCP : P ≤ C := by dsimp [C]; omega
  have hAC : A ≤ (C:ℝ) := hK.le.trans (by exact_mod_cast (show K ≤ C by dsimp [C]; omega))
  refine ⟨C,by dsimp [C]; omega,?_⟩
  intro N hN p q u hu l hl
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc : (2:ℝ)^J*(2*M:ℕ)^J*allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J ≤
      (C:ℝ)*(N:ℝ)^C := by
    calc
      _ ≤ (2:ℝ)^J*(2*M:ℕ)^J*((2*(4:ℝ)^J*(2*M:ℕ)^J)^(2^J-1)*(N:ℝ)^P) := by
        apply mul_le_mul_of_nonneg_left (allBranchExterior_inverse_jet_polynomial M J N hM hN)
        positivity
      _ = A*(N:ℝ)^P := by dsimp [A]; ring
      _ ≤ (C:ℝ)*(N:ℝ)^C := mul_le_mul hAC (pow_le_pow_right₀ hNr hCP) (by positivity) (by positivity)
  exact (allBranchExterior_weight_jet_raw M J hM hJ p q u hu l hl).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))

end
end IsingBulk.Tail
