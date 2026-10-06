import IsingBulk.Tail.MicrocoreAmplitudeGrowth
import IsingBulk.Tail.AllBranchExteriorOriginalNumerator
import IsingBulk.Tail.AllBranchExteriorPhaseUpper

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.First

theorem allBranchExterior_original_amplitude_jets (d : LocalBranchData) (J : ℕ) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ N : ℕ, 1 ≤ N → ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) →
      JetBound (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2)
        (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) J (Real.exp (A*(N:ℝ)^2)) := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖radialParameter d.theta 0‖ ≠ 0
    rw [radialParameter_norm (by norm_num)]
    norm_num
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hc : |Real.cos d.thetaB| < 1 := by
    have hh := Real.sin_sq_add_cos_sq d.thetaB
    have hs : 0 < Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨C,R,hC,hR,hf⟩ := micro_factor_bounds_uniform s₀ (Real.cos d.thetaB) hs₀ hS hc J
  obtain ⟨A,hA,hbudget⟩ := microAmplitudeBudget_exp J C hC
  obtain ⟨rφ,Cφ,hrφ,_,hφ⟩ := original_phase_small_radius d R hR
  let r := min R rφ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_left _ _)
  have hrφ' : r < rφ := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_right _ _)
  refine ⟨A,r,hA,hr,?_⟩
  intro ε hε hεr N hN u hu
  have hs : ‖radialParameter d.theta ε-s₀‖ < R := by
    rw [radialParameter_sub_zero_norm d.theta ε hε.le]
    exact hεr.trans_lt hrR
  have hph : ∀ i, ‖originalPhase d ε (u i)‖ < R :=
    fun i => (hφ ε r (u i) hε hεr hrφ' (hu i)).2
  exact (micro_amplitude_jet_product_budget _ J C hC (hf N _ _ hs hph)).mono le_rfl (hbudget N hN)

def allBranchExteriorNearNumeratorCost (A : ℝ) (J N : ℕ) : ℝ :=
  (2:ℝ)^(2*J)*(8:ℝ)^(N.choose 2)*((N.choose 2:ℝ)+1)^J*Real.exp (A*(N:ℝ)^2)

/-- The unfactored numerator retains its full natural collision power on each
common-sign cell, with the amplitude bound fixed before the cell scale. -/
theorem allBranchExterior_original_near_numerator {d : LocalBranchData} (B : BranchEstimates d) (J : ℕ) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ,
      1 ≤ N → J ≤ N*(N-1) → ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) →
      ∀ a H : ℝ, 0 < a → 1 ≤ H → B.magnitudeUpper/Real.sqrt a ≤ H →
      ((∀ i, a ≤ u i) ∨ (∀ i, u i ≤ -a)) →
      0 < allBranchExteriorDiameter u → H*allBranchExteriorDiameter u ≤ 1 →
      ∀ l : List (Option (Fin N)), l.length ≤ J →
      ‖numeratorJet l (unfactoredNumerator (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε,fun i => originalPhase d ε (u i))‖ ≤
        allBranchExteriorNearNumeratorCost A J N*
          (H*allBranchExteriorDiameter u)^(N*(N-1)-(spatialWord l).length) := by
  obtain ⟨A,rA,hA,hrA,hamp⟩ := allBranchExterior_original_amplitude_jets d J
  let r := min rA (min B.r B.ε₀)
  have hr : 0 < r := lt_min hrA (lt_min B.r_pos B.ε₀_pos)
  refine ⟨A,r,hA,hr,?_⟩
  intro ε hε hεr N hN hJN u hu a H ha hH hHmag hsign hdiam hHD l hl
  have hrA' : r ≤ rA := min_le_left _ _
  have hrB : r ≤ B.r := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r ≤ B.ε₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hjet := hamp ε hε (hεr.trans hrA') N hN u (fun i => (hu i).trans hrA')
  have hphase := allBranchExterior_common_sign_phase_diameter B ε a u hε (hεr.trans hre) ha
    (fun i => (hu i).trans hrB) hsign
  have hφ (p q : Fin N) : ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖ ≤
      2*(H*allBranchExteriorDiameter u) := by
    have hh := (hphase p q).trans (mul_le_mul_of_nonneg_right hHmag hdiam.le)
    have hpos : 0 ≤ H*allBranchExteriorDiameter u := mul_nonneg (zero_le_one.trans hH) hdiam.le
    linarith
  have hb := allBranchExterior_near_mixed_numerator_bound (mul_pos (zero_lt_one.trans_le hH) hdiam) hHD
    (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2)
    (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) J (Real.exp (A*(N:ℝ)^2)) hjet hφ l hl
  have hsp : (spatialWord l).length ≤ N*(N-1) := by
    have hh := mixed_word_degree l
    omega
  have he : ((N*(N-1):ℕ):ℤ)-((spatialWord l).length:ℤ)=((N*(N-1)-(spatialWord l).length:ℕ):ℤ) := by omega
  rw [he,zpow_natCast] at hb
  exact hb

end
end IsingBulk.Tail
