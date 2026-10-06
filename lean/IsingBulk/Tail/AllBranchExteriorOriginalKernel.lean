import IsingBulk.Tail.AllBranchExteriorKernelFloor
import IsingBulk.Tail.OriginalCurrentRootModulus
import IsingBulk.Tail.OriginalMicrocoreChart
import IsingBulk.Tail.MicrocoreArclength

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

/-- The original-circle kernel floor is attached to the genuine radial
chart. The zero homotopy parameter makes the auxiliary selector irrelevant. -/
theorem allBranchExterior_original_kernel_floor (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ u : Fin (n+1) → ℝ, (∀ i, |u i| ≤ r) →
      ‖regularKernel (radialParameter d.theta ε)
        (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖⁻¹ ≤
      4*twoPhaseKernel (d.c₀*ε) (a*ε)
        ((∑ i, u i)-(n+1:ℝ)*d.thetaB,∑ i, (originalPhase d ε (u i)).re) := by
  let f : SelectorFunctions := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩
  have hθ : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨δ,e,a,hδ,_,he,_,ha,hroot⟩ := original_current_root_modulus d.theta d.c₀ 0 hθ d.c₀_pos hcsmall
    le_rfl f (by intro; rfl) (by intro; norm_num [f]) (by intro; rfl)
    (by intro; norm_num [f]) (by intros; rfl) (by intros; rfl)
  obtain ⟨rC,hrC,hchart⟩ := original_microcore_chart d
  let r := min e rC/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < e := (half_lt_self (lt_min he hrC)).trans_le (min_le_left _ _)
  have hrc : r < rC := (half_lt_self (lt_min he hrC)).trans_le (min_le_right _ _)
  refine ⟨a,r,ha,hr,?_⟩
  intro ε hε hεr n u hu
  let s := radialParameter d.theta ε
  let v := -d.c₀*ε
  have hp := hchart ε hε (hεr.trans_lt hrc) n u (fun i => (hu i).trans_lt hrc)
  have hz := (hroot (n+1) (by omega) ε 0 hε (hεr.trans_lt hre) le_rfl (by norm_num)
    (fun i => u i-d.thetaB) s (by dsimp [s]; simpa using (mul_nonneg hδ.le hε.le))).2
  have heq : regularZProduct s (chartMap v d.thetaB s u)=
      coordinateProduct (fun i => selectedContinuedRoot s
        (deformedPoint f (Real.exp (-d.c₀*ε)) 0 0 (fun i => u i-d.thetaB) i)) := by
    rw [regularZProduct_eq_prod,coordinateProduct,deformedPoint_zero]
    apply Finset.prod_congr rfl
    intro i _
    change Complex.exp (-Complex.I*chartPhase s v d.thetaB (u i:ℂ))=
      selectedContinuedRoot s (anglePoint (Real.exp v) (u i-d.thetaB))
    rw [anglePoint_eq_angularY]
    unfold selectedContinuedRoot
    change Complex.exp (-Complex.I*chartPhase s v d.thetaB (u i:ℂ))=continuedRoot (chartW s v d.thetaB (u i:ℂ))
    rw [continuedRoot_eq_interiorRoot (hp.im_pos i)]
    exact (chart_root_eq_physical s v d.thetaB (u i:ℂ)).symm
  rw [← heq] at hz
  have hze : ‖regularZProduct s (chartMap v d.thetaB s u)‖ ≤ Real.exp (-(a*ε)) := by
    apply hz.trans
    apply Real.exp_le_exp.mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    push_cast
    have hprod : 0 ≤ a*ε*(n:ℝ) := by positivity
    nlinarith
  have hh := allBranchExterior_regular_kernel_floor v d.thetaB s u
    (by dsimp [v]; nlinarith [d.c₀_pos]) hp.g_pos (mul_pos ha hε) hze
  rw [show -v=d.c₀*ε by dsimp [v]; ring] at hh
  simpa only [s,v,original_chartMap_eq] using hh

end
end IsingBulk.Tail
