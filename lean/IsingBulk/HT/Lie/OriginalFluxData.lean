import IsingBulk.HT.Lie.SignedFluxTerms
import IsingBulk.Tail.AllBranchExteriorOriginalAmplitude
import IsingBulk.Tail.AllBranchExteriorCoefficientBounds
import IsingBulk.Tail.AllBranchExteriorPoint

/-! Actual original-chart bounds needed by geometric collision fluxes.
The radius and analytic scalar budgets precede particle number. At fixed
epsilon the phase is Lipschitz across the branch center itself, so the
full-collision flux does not require deleting that center a second time. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail Set
open scoped Topology

/-- Uniform scalar data includes the selected diagonal. -/
theorem original_scalar_bounds (d : LocalBranchData) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ N : ℕ, ∀ p q : Fin N, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) →
      ScalarBounds p q (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) J C := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖radialParameter d.theta 0‖ ≠ 0
    rw [radialParameter_norm (by norm_num)]
    norm_num
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hc : |Real.cos d.thetaB| < 1 := by
    have hs : 0 < Real.sin d.thetaB := d.a_pos
    have hh := Real.sin_sq_add_cos_sq d.thetaB
    rw [abs_lt]
    constructor <;> nlinarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨C,hC,U,P,hU,hsU,hP,hsP,hscalar⟩ :=
    scalar_bounds_uniform s₀ (Real.cos d.thetaB) hs₀ hS hc J
  obtain ⟨rU,hrU,hsubU⟩ := Metric.isOpen_iff.mp hU (s₀,0) hsU
  obtain ⟨rP,hrP,hsubP⟩ := Metric.isOpen_iff.mp hP (s₀,0,0) hsP
  let R := min rU rP
  have hR : 0 < R := lt_min hrU hrP
  obtain ⟨rφ,Cφ,hrφ,_,hφ⟩ := original_phase_small_radius d R hR
  let r := min R rφ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_left _ _)
  have hrφ' : r < rφ := (half_lt_self (lt_min hR hrφ)).trans_le (min_le_right _ _)
  refine ⟨C,r,hC,hr,?_⟩
  intro ε hε hεr N p q u hu
  have hs : ‖radialParameter d.theta ε-s₀‖ < R := by
    rw [radialParameter_sub_zero_norm d.theta ε hε.le]
    exact hεr.trans_lt hrR
  have hphase (i : Fin N) : ‖originalPhase d ε (u i)‖ < R :=
    (hφ ε r (u i) hε hεr hrφ' (hu i)).2
  apply hscalar N p q _
  · intro i
    apply hsubU
    simpa [Metric.mem_ball,Prod.dist_eq,dist_eq_norm] using
      And.intro (hs.trans_le (min_le_left _ _)) ((hphase i).trans_le (min_le_left _ _))
  · apply hsubP
    simpa [Metric.mem_ball,Prod.dist_eq,dist_eq_norm] using
      And.intro (hs.trans_le (min_le_right _ _))
        (And.intro ((hphase p).trans_le (min_le_right _ _)) ((hphase q).trans_le (min_le_right _ _)))

/-- No common-sign restriction is needed in the fixed-epsilon puncture limit. -/
theorem fixed_epsilon_phase_difference_upper {d : LocalBranchData} (B : BranchEstimates d)
    (ε u v : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hu : |u| ≤ B.r) (hv : |v| ≤ B.r) :
    ‖originalPhase d ε v-originalPhase d ε u‖ ≤
      (B.magnitudeUpper/Real.sqrt ε)*|v-u| := by
  have hseg (x : ℝ) (hx : x∈uIcc u v) : |x| ≤ B.r := by
    rw [abs_le]
    exact ⟨(le_min (abs_le.mp hu).1 (abs_le.mp hv).1).trans hx.1,
      hx.2.trans (max_le (abs_le.mp hu).2 (abs_le.mp hv).2)⟩
  have hd (x : ℝ) (hx : x∈uIcc u v) : DifferentiableAt ℝ (originalPhase d ε) x := by
    obtain ⟨hr,hi⟩ := B.quadrant ε x hε hεr (hseg x hx)
    exact (currentPhase_hasDerivAt d ε 0 x hr hi).differentiableAt
  have hb (x : ℝ) (hx : x∈uIcc u v) :
      ‖deriv (originalPhase d ε) x‖ ≤ B.magnitudeUpper/Real.sqrt ε := by
    apply (B.magnitude ε x hε hεr (hseg x hx)).2.trans
    exact div_le_div_of_nonneg_left B.magnitudeUpper_pos.le (Real.sqrt_pos.mpr hε)
      (Real.sqrt_le_sqrt (by linarith [abs_nonneg x]))
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le hd hb
    (convex_uIcc u v) left_mem_uIcc right_mem_uIcc

/-- Actual unfactored numerator has the full collision power, including
at centers of either sign and at center zero, for each fixed epsilon. -/
theorem fixed_epsilon_numerator_power {d : LocalBranchData} (B : BranchEstimates d) (J : ℕ) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ N : ℕ, 1 ≤ N → J ≤ N*(N-1) → ∀ u : Fin N → ℝ,
      (∀ i, |u i| ≤ r) → ∀ H : ℝ, 1 ≤ H → B.magnitudeUpper/Real.sqrt ε ≤ H →
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
  intro ε hε hεr N hN hJN u hu H hH hHmag hdiam hHD l hl
  have hrA' : r ≤ rA := min_le_left _ _
  have hrB : r ≤ B.r := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r ≤ B.ε₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hjet := hamp ε hε (hεr.trans hrA') N hN u (fun i => (hu i).trans hrA')
  have hφ (p q : Fin N) : ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖ ≤
      2*(H*allBranchExteriorDiameter u) := by
    have hp := fixed_epsilon_phase_difference_upper B ε (u q) (u p) hε
      (hεr.trans hre) ((hu q).trans hrB) ((hu p).trans hrB)
    have hh := hp.trans (mul_le_mul hHmag
      (allBranchExterior_pair_le_diameter u p q) (abs_nonneg _)
      (zero_le_one.trans hH))
    have hpos : 0 ≤ H*allBranchExteriorDiameter u := mul_nonneg (zero_le_one.trans hH) hdiam.le
    linarith
  have hb := allBranchExterior_near_mixed_numerator_bound
    (mul_pos (zero_lt_one.trans_le hH) hdiam) hHD
    (fun t : ℂ × (Fin N → ℂ) => microRegularAmplitude t.1 t.2)
    (radialParameter d.theta ε,fun i => originalPhase d ε (u i)) J
    (Real.exp (A*(N:ℝ)^2)) hjet hφ l hl
  have hsp : (spatialWord l).length ≤ N*(N-1) := by
    have hh := mixed_word_degree l
    omega
  have he : ((N*(N-1):ℕ):ℤ)-((spatialWord l).length:ℤ)=
      ((N*(N-1)-(spatialWord l).length:ℕ):ℤ) := by omega
  rw [he,zpow_natCast] at hb
  exact hb

end
end IsingBulk.HT.Lie
