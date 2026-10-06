import IsingBulk.Tail.ConstructedCurrentSupport
import IsingBulk.Tail.ProtectedBranchPair
import IsingBulk.Tail.SelectedFDiskSupport
import IsingBulk.Tail.OriginalGlobalDisk

/-! Literal original K closed support and lower-branch complete-pair
contraction on the original c epsilon disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology

theorem constructed_original_support_sine_upper {N : ℕ} (b η α : ℝ) (hα : 0 < α)
    (i : Fin N) : tsupport (angularSelector (constructedSelector b η α)) ⊆
      {θ : Fin N → ℝ | Real.sin (θ i) ≤ 3*α/2} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hn
    have hs : 3*α/2 < Real.sin (θ i) := lt_of_not_ge hn
    have ha : (constructedSelector b η α).a (θ i)=1 := thresholdStep_one (by linarith) hs.le
    apply hθ
    unfold angularSelector selectorWeight
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [ha,sub_self])
  · exact isClosed_le (Real.continuous_sin.comp (continuous_apply i)) continuous_const

theorem original_lower_branch_complete_pair (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r c e : ℝ, 0 < r ∧ 0 < c ∧ 0 < e ∧ ∀ eps u v : ℝ, ∀ s : ℂ,
      0 < eps → eps < e → |u| < r → |v| < r →
      ‖s-radialParameter d.theta eps‖ ≤ c*eps →
      let y := radialAnglePoint (-d.c₀*eps) (u-d.thetaB)
      let y' := radialAnglePoint (-d.c₀*eps) (v-d.thetaB)
      ‖canceledPair y y' (selectedContinuedRoot s y) (selectedContinuedRoot s y')‖ ≤ 1/2 := by
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨c,e,hc,_hc1,he,_he1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  obtain ⟨r,hr,hpair⟩ := lower_branch_y_pair_strict d (q := 1/2) (by norm_num)
  refine ⟨r,c,min e r,hr,hc,lt_min he hr,?_⟩
  intro eps u v s heps hepslt hu hv hsd
  have hyeq (a : ℝ) : plateauY d.c₀ eps 1 0 d.thetaB a=radialAnglePoint (-d.c₀*eps) (a-d.thetaB) := by
    unfold plateauY radialAnglePoint
    congr 1
    push_cast
    ring
  obtain ⟨hygap,hypair⟩ := hpair eps 0 u v
    (by simpa [abs_of_pos heps] using hepslt.trans_le (min_le_right _ _))
    (by simpa using hr) hu hv
  rw [hyeq u,hyeq v] at hygap hypair
  let y := radialAnglePoint (-d.c₀*eps) (u-d.thetaB)
  let y' := radialAnglePoint (-d.c₀*eps) (v-d.thetaB)
  have hWi := hupper eps heps (hepslt.trans_le (min_le_left _ _)) s hsd (u-d.thetaB)
  have hWj := hupper eps heps (hepslt.trans_le (min_le_left _ _)) s hsd (v-d.thetaB)
  have hz : selectedContinuedRoot s y=interiorRoot (sourceW s y) := continuedRoot_eq_interiorRoot hWi
  have hz' : selectedContinuedRoot s y'=interiorRoot (sourceW s y') := continuedRoot_eq_interiorRoot hWj
  have hp : ‖pairKernel (selectedContinuedRoot s y) (selectedContinuedRoot s y')‖ ≤ 1 := by
    rw [hz,hz']
    exact schur_norm_le (interiorRoot_norm_lt_one hWi).le (interiorRoot_norm_lt_one hWj).le
      (mul_nonneg_of_nonpos_of_nonpos (interiorRoot_lower_im hWi).le (interiorRoot_lower_im hWj).le)
  have hquad (a : ℂ) : (selectedContinuedRoot s a)^2-(2*sourceS s-a-a⁻¹)*selectedContinuedRoot s a+1=0 := by
    have hh := continuedRoot_quadratic (sourceW s a)
    dsimp [selectedContinuedRoot,sourceW] at hh ⊢
    linear_combination hh
  have hi := source_pair_identity (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (continuedRoot_nonzero _) (continuedRoot_nonzero _) (hquad y) (hquad y') hygap
    (continuedRoot_pair_gap (Or.inl (Or.inl hWi)) (Or.inl (Or.inl hWj)))
  change ‖canceledPair y y' (selectedContinuedRoot s y) (selectedContinuedRoot s y')‖ ≤ _
  change pairKernel (selectedContinuedRoot s y) (selectedContinuedRoot s y')*pairKernel y y'=canceledPair y y' (selectedContinuedRoot s y) (selectedContinuedRoot s y') at hi
  rw [← hi,norm_mul]
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa only [one_mul,y,y'] using hypair.le)

theorem radialAnglePoint_sub_two_pi (v θ : ℝ) :
    radialAnglePoint v (θ-2*Real.pi)=radialAnglePoint v θ := by
  apply Complex.ext <;> simp [radialAnglePoint,Complex.exp_re,Complex.exp_im]

theorem original_actual_branch_pair_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ c e : ℝ, 0 < η₀ ∧ 0 < c ∧ 0 < e ∧ ∀ η eps θ φ : ℝ, ∀ s : ℂ,
      0 < η → η < η₀ → 0 < eps → eps < e →
      0 ≤ θ → θ ≤ 2*Real.pi → 0 ≤ φ → φ ≤ 2*Real.pi →
      lowerChord d.thetaB θ < η^2/2 → lowerChord d.thetaB φ < η^2/2 →
      ‖s-radialParameter d.theta eps‖ ≤ c*eps →
      let y := radialAnglePoint (-d.c₀*eps) θ
      let y' := radialAnglePoint (-d.c₀*eps) φ
      ‖canceledPair y y' (selectedContinuedRoot s y) (selectedContinuedRoot s y')‖ ≤ 1/2 := by
  obtain ⟨r,c,e,hr,hc,he,hpair⟩ := original_lower_branch_complete_pair d hcsmall
  obtain ⟨η₀,hη₀,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  refine ⟨η₀,c,e,hη₀,hc,he,?_⟩
  intro η eps θ φ s hη hηlt heps hepslt hθ0 hθ1 hφ0 hφ1 hθ hφ hs
  have hcore (u : ℝ) (hu0 : 0≤u) (hu1 : u≤2*Real.pi) (hu : lowerChord d.thetaB u<η^2/2) :
      |u+d.thetaB-2*Real.pi|<r := by
    apply hcoord u hu0 hu1
    have hh := pow_le_pow_left₀ hη.le hηlt.le 2
    linarith [sq_nonneg η]
  have hh := hpair eps (θ+d.thetaB-2*Real.pi) (φ+d.thetaB-2*Real.pi) s heps hepslt
    (hcore θ hθ0 hθ1 hθ) (hcore φ hφ0 hφ1 hφ) hs
  have heq (u : ℝ) : u+d.thetaB-2*Real.pi-d.thetaB=u-2*Real.pi := by ring
  simpa only [heq,radialAnglePoint_sub_two_pi] using hh


end
end IsingBulk.Tail
