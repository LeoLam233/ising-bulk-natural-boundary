import IsingBulk.Tail.MixedResidualJetFamily
import IsingBulk.Tail.MixedActiveVelocity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Common actual-source jet constants for both transport residuals and
every angular cutoff coefficient. The dimension loss is only linear. -/
theorem mixed_actual_coefficient_jet_family (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 1≤C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      sigma j=2 → sigma q≠2 →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let J := mixedBranchIndexSet sigma
      ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 →
      JetBound (mixedActiveBranchResidual J j q s φ y) 0 (order+1) ((N:ℝ)*C) ∧
      JetBound (mixedActiveCompactResidual J j q s φ y) 0 (order+1) ((N:ℝ)*C) ∧
      ∀ i,JetBound (mixedActiveAngularVelocity J j q s φ y i) 0 order ((N:ℝ)*C) := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀≠0 := norm_ne_zero_iff.mp (by
    change ‖radialParameter d.theta 0‖≠0
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hcos : |Real.cos d.thetaB|<1 := by
    have hsin : 0<Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [hsin,Real.sin_sq_add_cos_sq d.thetaB,
      Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨iA,cA,eA,tA,A,hiA,hiAcap,hcA,heA,htA,_hA,hBranchA⟩ :=
    mixed_actual_branch_function_jets d hcsmall regularA
      (regularA_analytic_base s₀ (Real.cos d.thetaB) hs₀ hS hcos) cap hcap order
  obtain ⟨iB,cB,eB,tB,B,hiB,_,hcB,heB,htB,_hB,hBranchB⟩ :=
    mixed_actual_branch_function_jets d hcsmall mixedInverseSlope
      (mixedInverseSlope_analytic_base s₀ (Real.cos d.thetaB) hs₀ hS hcos) cap hcap order
  obtain ⟨iR,hiR,_,hResiduals⟩ := mixed_actual_separated_residual_jet_family d hcsmall cap hcap (order+1)
  refine ⟨min iA (min iB iR),lt_min hiA (lt_min hiB hiR),(min_le_left _ _).trans hiAcap,?_⟩
  intro inner hi hinner
  obtain ⟨cR,eR,tR,R,hcR,heR,htR,_hR,hResidual⟩ :=
    hResiduals inner hi (hinner.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D := max 1 (max A (max B R))
  have hD : 1≤D := le_max_left _ _
  have hD0 : 0≤D := zero_le_one.trans hD
  have hAD : A≤D := (le_max_left _ _).trans (le_max_right _ _)
  have hBD : B≤D := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRD : R≤D := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  let C := 2*D+2^order*D^2
  have hDC : D≤C := by dsimp [C]; nlinarith [show 0≤(2:ℝ)^order*D^2 by positivity]
  refine ⟨min cA (min cB cR),min eA (min eB eR),min tA (min tB tR),C,
    lt_min hcA (lt_min hcB hcR),lt_min heA (lt_min heB heR),lt_min htA (lt_min htB htR),hD.trans hDC,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hσj hσq hSource hsupp hs
  dsimp only
  intro hsep
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  have hsA := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsB := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsR := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  obtain ⟨hRj,hQj⟩ := hResidual η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hθ hσj hσq hSource hsupp hsR hsep
  have hRjD := hRj.mono le_rfl hRD
  have hQjD := hQj.mono le_rfl hRD
  have hscaled := mixed_active_scaled_residual_jets J j q s φ y (order+1) D hRjD hQjD
  have hprofile (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hAj (i : Fin N) (hiJ : i∈J) : JetBound (mixedActiveBranch regularA s φ i) 0 order D := by
    have hh := hBranchA η α hη hηsmall hα N eps τ lam θ i s hN heps
      (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
      ((hprofile i hiJ).trans (hinner.trans (min_le_left _ _))) hsA
    exact hh.mono le_rfl hAD
  have hBj : JetBound (mixedActiveBranch mixedInverseSlope s φ j) 0 order D := by
    have hh := hBranchB η α hη hηsmall hα N eps τ lam θ j s hN heps
      (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hl0 hl1
      (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      ((hprofile j hj).trans (hinner.trans ((min_le_right _ _).trans (min_le_left _ _)))) hsB
    exact hh.mono le_rfl hBD
  refine ⟨hscaled.1.mono le_rfl (mul_le_mul_of_nonneg_left hDC (Nat.cast_nonneg N)),
    hscaled.2.mono le_rfl (mul_le_mul_of_nonneg_left hDC (Nat.cast_nonneg N)),?_⟩
  intro i
  exact mixedActiveAngularVelocity_jet_bound hN J j q i s φ y order D hD0 hAj hBj
    (hRjD.mono (by omega) le_rfl) (hQjD.mono (by omega) le_rfl)

end
end IsingBulk.Tail
