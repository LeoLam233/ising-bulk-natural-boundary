import IsingBulk.Tail.AllBranchExteriorGuardJets
import IsingBulk.Tail.AllBranchExteriorWeightJets
import IsingBulk.Tail.AllBranchExteriorPoleAbsorption

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch Set Function
open scoped ContDiff

def allBranchGuardedPairWeight {N : ℕ} (M : ℕ) (h : ℝ) (p q : Fin N) (u : Fin N → ℝ) : ℝ :=
  allBranchExteriorPairWeight M p q u*allBranchSelectedGuard h p q u

theorem allBranchGuardedPairWeight_tsupport {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h) (p q : Fin N) :
    tsupport (allBranchGuardedPairWeight M h p q) ⊆ {u | h/2 ≤ |u p-u q|} :=
  tsupport_mul_subset_right.trans (allBranchSelectedGuard_tsupport hh p q)

theorem allBranchGuardedPairWeight_smooth {N : ℕ} (M : ℕ) {h : ℝ} (hh : 0 < h) (p q : Fin N) :
    ContDiff ℝ ∞ (allBranchGuardedPairWeight M h p q) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport (allBranchSelectedGuard h p q)
  · have hd : 0 < allBranchExteriorDiameter u :=
      (half_pos hh).trans_le ((allBranchSelectedGuard_tsupport hh p q hu).trans
        (allBranchExterior_pair_le_diameter u p q))
    exact (allBranchExterior_pairWeight_contDiffAt M p q u hd).mul
      (allBranchSelectedGuard_smooth h p q).contDiffAt
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hu
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with x hx
    change allBranchExteriorPairWeight M p q x*allBranchSelectedGuard h p q x=0
    simp only [hx,Pi.zero_apply,mul_zero]

theorem allBranchGuardedPairWeight_uniform_jets (M J : ℕ) (hM : 0 < M) (hJ : J < 2*M) :
    ∃ C : ℕ, 0 < C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ h : ℝ, 0 < h → ∀ p q : Fin N, ∀ u : Fin N → ℝ, u p ≠ u q →
      ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (allBranchGuardedPairWeight M h p q) u‖ ≤
        ((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M) := by
  obtain ⟨C,hC,hweight⟩ := allBranchExterior_weight_jets_uniform M J hM hJ
  obtain ⟨D,hD,hguard⟩ := allBranchSelectedGuard_distance_jets J
  refine ⟨C,hC,D,hD,?_⟩
  intro N hN h hh p q u hu l hl
  let δ := |u p-u q|
  let d := allBranchExteriorDiameter u
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hu)
  have hd : 0 < d := hδ.trans_le (allBranchExterior_pair_le_diameter u p q)
  let U := {x : Fin N → ℝ | allBranchExteriorWeightDenom M x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (allBranchExteriorWeightDenom_smooth M).continuous continuous_const
  have huU : u ∈ U := (allBranchExterior_weightDenom_pos M u hd).ne'
  have hf : ∀ x ∈ U, ContDiffAt ℝ ∞ (allBranchExteriorPairWeight M p q) x := by
    intro x hx
    exact (show ContDiff ℝ ∞ (fun y : Fin N → ℝ => (y p-y q)^(2*M)) by fun_prop).contDiffAt.div
      (allBranchExteriorWeightDenom_smooth M).contDiffAt hx
  have hF : AllBranchExteriorScaledJets (allBranchExteriorPairWeight M p q) u J δ
      (((C:ℝ)*(N:ℝ)^C)/d^(2*M)) ((2*M:ℕ):ℤ) := by
    refine ⟨by positivity,?_⟩
    intro k hk
    have he : ((2*M:ℕ):ℤ)-(k.length:ℤ)=((2*M-k.length:ℕ):ℤ) := by omega
    rw [he,zpow_natCast]
    apply (hweight N hN p q u hd k hk).trans_eq
    dsimp [δ,d]
    ring
  have hG : AllBranchExteriorScaledJets (allBranchSelectedGuard h p q) u J δ D 0 := by
    refine ⟨zero_le_one.trans hD,?_⟩
    intro k hk
    simpa only [zero_sub,zpow_neg,zpow_natCast,inv_pow] using hguard N h hh p q u hu k hk
  have hb := (allBranchExterior_scaled_product (allBranchExteriorPairWeight M p q)
    (allBranchSelectedGuard h p q) hU hf (fun _ _ => (allBranchSelectedGuard_smooth h p q).contDiffAt)
    u huU J δ _ D hδ _ 0 hF hG).bound l hl
  have he : ((2*M:ℕ):ℤ)+0-(l.length:ℤ)=((2*M-l.length:ℕ):ℤ) := by omega
  rw [he,zpow_natCast] at hb
  apply hb.trans_eq
  dsimp [δ,d]
  ring

theorem allBranchGuardedPairWeight_pole_uniform (d₀ : LocalBranchData)
    (M J : ℕ) (hM : 0 < M) (hJ : J < 2*M) :
    ∃ C : ℕ, 0 < C ∧ ∃ D c r : ℝ, 1 ≤ D ∧ 0 < c ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N →
      ∀ h : ℝ, 0 < h → ∀ p q : Fin N, ∀ u : Fin N → ℝ,
      (∀ i, |u i| ≤ r) → u p ≠ u q → ∀ l : List (Fin N), l.length ≤ J →
      ∀ m : ℕ, m+l.length ≤ 2*M →
      ‖cutoffJet l (allBranchGuardedPairWeight M h p q) u‖/
        ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m ≤
        ((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*(c⁻¹)^m/(allBranchExteriorDiameter u)^(l.length+m) := by
  obtain ⟨C,hC,D,hD,hweight⟩ := allBranchGuardedPairWeight_uniform_jets M J hM hJ
  obtain ⟨c,r,hc,hr,hsep⟩ := original_phase_difference_lower d₀
  refine ⟨C,hC,D,c,r,hD,hc,hr,?_⟩
  intro ε hε hεr N hN h hh p q u hu hpq l hl m hm
  have hδ : 0 < |u p-u q| := abs_pos.mpr (sub_ne_zero.mpr hpq)
  have hdiam := allBranchExterior_pair_le_diameter u p q
  have hw := hweight N hN h hh p q u hpq l hl
  have hz := hsep ε (u p) (u q) hε hεr (hu p) (hu q)
  have hs := allBranchExterior_scalar_pole_absorption |u p-u q|
    (allBranchExteriorDiameter u) ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖
    c (2*M-l.length) l.length m hδ hdiam hc hz (by omega)
  have he : 2*M-l.length+l.length=2*M := by omega
  rw [he] at hs
  calc
    _ ≤ (((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M))/
        ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m :=
      div_le_div_of_nonneg_right hw (by positivity)
    _ = ((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*
        ((|u p-u q|^(2*M-l.length)/(allBranchExteriorDiameter u)^(2*M))/
          ‖originalPhase d₀ ε (u p)-originalPhase d₀ ε (u q)‖^m) := by ring
    _ ≤ ((2:ℝ)^J*(C:ℝ)*(N:ℝ)^C*D)*((c⁻¹)^m/(allBranchExteriorDiameter u)^(l.length+m)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end
end IsingBulk.Tail
