import IsingBulk.Tail.AllBranchExteriorWeightJets
import IsingBulk.Tail.CompactAveragedField

/-! All-order real jets of the actual quadratic averaging denominator. The
vanishing of derivatives above polynomial degree preserves sharp scaling. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped BigOperators ContDiff
set_option maxHeartbeats 1600000

theorem allBranchExterior_linear_power_scaled_all_orders {N : ℕ} (p q : Fin N) (m J : ℕ)
    (hm : 1≤m) (u : Fin N → ℝ) (d : ℝ) (hd : 0<d) (hu : |u p-u q|≤d) :
    AllBranchExteriorScaledJets (fun x => (x p-x q)^m) u J d ((m:ℝ)^J) (m:ℤ) := by
  refine ⟨by positivity,?_⟩
  intro l hl
  have hn := coordinate_difference_jet_norm p q m l u
  by_cases hlen : l.length≤m
  · have hc : (m.descFactorial l.length:ℝ)≤(m:ℝ)^J := by
      exact_mod_cast (Nat.descFactorial_le_pow m l.length).trans (Nat.pow_le_pow_right hm hl)
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hu (m-l.length)
    have he : (m:ℤ)-(l.length:ℤ)=((m-l.length:ℕ):ℤ) := by omega
    rw [he,zpow_natCast]
    exact hn.trans (mul_le_mul hc hpow (pow_nonneg (abs_nonneg _) _) (by positivity))
  · have hfac : m.descFactorial l.length=0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hfac,Nat.cast_zero,zero_mul] at hn
    exact hn.trans (by positivity)

theorem allBranchExterior_denominator_scaled_all_orders {N : ℕ} (M J : ℕ) (hM : 0 < M)
    (u : Fin N → ℝ) (hu : 0 < allBranchExteriorDiameter u) :
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
    exact (allBranchExterior_linear_power_scaled_all_orders p.1 p.2 (2*M) J (by omega) u _ hu
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

theorem allBranchExterior_denominator_inverse_scaled_all_orders {N : ℕ} (M J : ℕ) (hM : 0 < M)
    (u : Fin N → ℝ) (hu : 0 < allBranchExteriorDiameter u) :
    AllBranchExteriorScaledJets (fun x => (allBranchExteriorWeightDenom M x)⁻¹) u J
      (allBranchExteriorDiameter u)
      (allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2*M:ℕ)^J) J) (-(2*M:ℕ)) := by
  let U := {x : Fin N → ℝ | allBranchExteriorWeightDenom M x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (allBranchExteriorWeightDenom_smooth M).continuous continuous_const
  apply allBranchExterior_scaled_inverse (allBranchExteriorWeightDenom M) hU
    (fun x _ => (allBranchExteriorWeightDenom_smooth M).contDiffAt) (fun _ hx => hx) u
    (allBranchExterior_weightDenom_pos M u hu).ne' J _ _ hu (2*M:ℕ)
    (allBranchExterior_denominator_scaled_all_orders M J hM u hu)
  simpa only [zpow_natCast] using allBranchExterior_weightDenom_diameter_lower M u hu


theorem fullAngularPairSet_eq_ordered (N : ℕ) :
    fullAngularPairSet N=orderedIndexPairs (Finset.univ : Finset (Fin N)) := by
  ext p
  simp [fullAngularPairSet,orderedIndexPairs]

theorem full_pair_square_mass_eq_denominator {N : ℕ} (x : Fin N → ℝ) :
    pairSquareMass (fullAngularPairSet N) (fun p => x p.1-x p.2)=allBranchExteriorWeightDenom 1 x := by
  simp only [pairSquareMass,allBranchExteriorWeightDenom,fullAngularPairSet_eq_ordered,Nat.mul_one]

theorem full_pair_square_mass_inverse_scaled {N : ℕ} (J : ℕ) (x : Fin N → ℝ)
    (hx : 0<allBranchExteriorDiameter x) :
    AllBranchExteriorScaledJets
      (fun y => (pairSquareMass (fullAngularPairSet N) (fun p => y p.1-y p.2))⁻¹)
      x J (allBranchExteriorDiameter x)
      (allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2:ℝ)^J) J) (-2) := by
  simp_rw [full_pair_square_mass_eq_denominator]
  simpa using allBranchExterior_denominator_inverse_scaled_all_orders 1 J (by decide) x hx


def angularPairMass {N : ℕ} (P : Finset (Fin N × Fin N)) (x : Fin N → ℝ) : ℝ :=
  pairSquareMass P (fun p => x p.1-x p.2)

def angularPairMassScale {N : ℕ} (P : Finset (Fin N × Fin N)) (x : Fin N → ℝ) : ℝ :=
  Real.sqrt (angularPairMass P x)

theorem angularPairMass_smooth {N : ℕ} (P : Finset (Fin N × Fin N)) :
    ContDiff ℝ ∞ (angularPairMass P) := by
  unfold angularPairMass pairSquareMass
  fun_prop

theorem angularPairMass_pair_bound {N : ℕ} (P : Finset (Fin N × Fin N))
    (x : Fin N → ℝ) (p : Fin N × Fin N) (hp : p∈P) :
    |x p.1-x p.2|≤angularPairMassScale P x := by
  have hs : 0≤angularPairMass P x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh : (x p.1-x p.2)^2≤angularPairMass P x := by
    change (x p.1-x p.2)^2≤∑ q∈P, (x q.1-x q.2)^2
    exact Finset.single_le_sum (fun q _ => sq_nonneg (x q.1-x q.2)) hp
  have he := Real.sq_sqrt hs
  have hz := Real.sqrt_nonneg (angularPairMass P x)
  dsimp [angularPairMassScale]
  nlinarith [sq_abs (x p.1-x p.2),abs_nonneg (x p.1-x p.2)]

theorem angularPairMass_scaled {N : ℕ} (P : Finset (Fin N × Fin N)) (J : ℕ)
    (x : Fin N → ℝ) (hS : 0<angularPairMass P x) :
    AllBranchExteriorScaledJets (angularPairMass P) x J (angularPairMassScale P x)
      ((N:ℝ)^2*(2:ℝ)^J) 2 := by
  have hd : 0<angularPairMassScale P x := Real.sqrt_pos.mpr hS
  refine ⟨by positivity,?_⟩
  intro l hl
  unfold angularPairMass pairSquareMass
  rw [cutoffJet_finset_sum _ l _ isOpen_univ
    (fun p _ y _ => (show ContDiff ℝ ∞ (fun z : Fin N → ℝ => (z p.1-z p.2)^2) by fun_prop).contDiffAt)
    x (mem_univ x)]
  apply (norm_sum_le _ _).trans
  have hp : ∀ p∈P, ‖cutoffJet l (fun y : Fin N → ℝ => (y p.1-y p.2)^2) x‖≤
      (2:ℝ)^J*(angularPairMassScale P x)^(2-(l.length:ℤ)) := by
    intro p hp
    exact (allBranchExterior_linear_power_scaled_all_orders p.1 p.2 2 J (by decide) x _ hd
      (angularPairMass_pair_bound P x p hp)).bound l hl
  have hcard : P.card≤N^2 := by
    have hh := Finset.card_le_univ P
    simpa [pow_two] using hh
  have hcardR : (P.card:ℝ)≤(N:ℝ)^2 := by exact_mod_cast hcard
  calc
    _ ≤ ∑ _p∈P, (2:ℝ)^J*(angularPairMassScale P x)^(2-(l.length:ℤ)) :=
      Finset.sum_le_sum (fun p hpP => hp p hpP)
    _ = (P.card:ℝ)*((2:ℝ)^J*(angularPairMassScale P x)^(2-(l.length:ℤ))) := by simp
    _ ≤ (N:ℝ)^2*((2:ℝ)^J*(angularPairMassScale P x)^(2-(l.length:ℤ))) := by gcongr
    _ = _ := by ring

/-- All fixed orders for any allowed pair set, including the current free
pair set. The scale is its own mass square root; no free-coordinate reindexing
or motion of the distinguished coordinate is involved. -/
theorem angularPairMass_inverse_scaled {N : ℕ} (P : Finset (Fin N × Fin N)) (J : ℕ)
    (x : Fin N → ℝ) (hS : 0<angularPairMass P x) :
    AllBranchExteriorScaledJets (fun y => (angularPairMass P y)⁻¹) x J (angularPairMassScale P x)
      (allBranchExteriorInverseJetConstant ((N:ℝ)^2*(2:ℝ)^J) J) (-2) := by
  let U := {y : Fin N → ℝ | angularPairMass P y≠0}
  have hU : IsOpen U := isOpen_ne_fun (angularPairMass_smooth P).continuous continuous_const
  have hd : 0<angularPairMassScale P x := Real.sqrt_pos.mpr hS
  apply allBranchExterior_scaled_inverse (angularPairMass P) hU
    (fun _ _ => (angularPairMass_smooth P).contDiffAt) (fun _ hx => hx) x hS.ne' J _ _ hd 2
    (angularPairMass_scaled P J x hS)
  change (Real.sqrt (angularPairMass P x))^(2:ℤ)≤angularPairMass P x
  rw [zpow_ofNat,Real.sq_sqrt hS.le]

end
end IsingBulk.Tail
