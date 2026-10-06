import IsingBulk.Tail.BranchOneBody
import IsingBulk.Tail.BranchDiskPerturbation

/-! Actual original-disk one-body estimate with arbitrary occupancy. The
constant and disk precede τ, ε, t=λP/N and the branch angle. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First Filter
open scoped Topology

theorem original_disk_branch_onebody (d : LocalBranchData) :
    ∃ C δ r : ℝ, 0 < C ∧ 0 < δ ∧ 0 < r ∧
    ∀ τ ε t u : ℝ, ∀ s : ℂ,
      0 ≤ τ → τ < r → 0 < ε → ε < r → 0 ≤ t → t ≤ 1 → |u| < r →
      ‖s-radialParameter d.theta ε‖ ≤ δ*ε →
      ‖residueFactor (interiorRoot (IsingBulk.Branch.dispersion s
        (plateauY d.c₀ ε τ t d.thetaB u)))‖ ≤ C/Real.sqrt (|u|+ε) := by
  let d₁ := unitDeformationData d
  obtain ⟨c,rd,hc,hrd,hd⟩ := disk_branch_distance d₁
  obtain ⟨b,ri,hb,hri,hi⟩ := disk_branch_imaginary_margin d₁
  let κ := min c b
  have hκ : 0 < κ := lt_min hc hb
  obtain ⟨δ,hδ,htrace⟩ := radial_trace_disk_slack d.theta κ hκ
  have hcont : ContinuousAt (fun z : ℝ × ℝ × ℝ => ‖currentW d₁ z.1 z.2.1 z.2.2-1‖) 0 :=
    ((currentW_continuous d₁).sub continuousAt_const).norm
  have hzero : ‖currentW d₁ 0 0 0-1‖ < 1/4 := by rw [currentW_zero]; norm_num
  obtain ⟨rn,hrn,hn⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually_lt continuousAt_const hzero)
  let r := min rd (min ri (min rn (min 1 (1/(4*κ)))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r ≤ rd ∧ r ≤ ri ∧ r ≤ rn ∧ r ≤ 1 ∧ r ≤ 1/(4*κ) := by
    have hh : r ≤ min rd (min ri (min rn (min 1 (1/(4*κ))))) := le_rfl
    simpa only [le_min_iff] using hh
  refine ⟨1/Real.sqrt c,δ,r,by positivity,hδ,hr,?_⟩
  intro τ ε t u s hτ hτr hε hεr ht ht1 hur hs
  have hτt : 0 ≤ τ*t := mul_nonneg hτ ht
  have hτtr : τ*t < r := (mul_le_of_le_one_right hτ ht1).trans_lt hτr
  have hsκ := htrace ε hε (hεr.le.trans hrs.2.2.2.1) s hs
  have hsc : ‖(s+s⁻¹)-(radialParameter d₁.theta ε+(radialParameter d₁.theta ε)⁻¹)‖ ≤ c*ε :=
    hsκ.trans (mul_le_mul_of_nonneg_right (min_le_left c b) hε.le)
  have hsb : ‖(s+s⁻¹)-(radialParameter d₁.theta ε+(radialParameter d₁.theta ε)⁻¹)‖ ≤ b*ε :=
    hsκ.trans (mul_le_mul_of_nonneg_right (min_le_right c b) hε.le)
  let W := diskBranchW d₁ ε (τ*t) u s
  have hdist := hd ε (τ*t) u s hε (hεr.trans_le hrs.1) hτt
    (hτtr.trans_le hrs.1) (hur.trans_le hrs.1) hsc
  have him := hi ε (τ*t) u s hε (hεr.trans_le hrs.2.1) hτt
    (hτtr.trans_le hrs.2.1) (hur.trans_le hrs.2.1) hsb
  have hWim : 0 < W.im := by
    change b*(ε+1*(τ*t)) ≤ W.im at him
    nlinarith [mul_nonneg hb.le hτt]
  have hnear : ‖currentW d₁ ε (τ*t) u-1‖ < 1/4 := by
    apply hn (y := (ε,τ*t,u))
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg hτt,abs_of_nonneg hτ,abs_of_nonneg ht]
      using And.intro (hεr.trans_le hrs.2.2.1)
        (And.intro (hτtr.trans_le hrs.2.2.1) (hur.trans_le hrs.2.2.1))
  have hdiff : ‖W-currentW d₁ ε (τ*t) u‖ ≤ κ*ε := by
    dsimp only [W]
    rw [diskBranchW_difference]
    exact hsκ
  have hκeps : κ*ε ≤ 1/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*κ by positivity)).mp hrs.2.2.2.2
    nlinarith
  have hWnear : ‖W-1‖ < 1/2 := by
    have hh := norm_add_le (W-currentW d₁ ε (τ*t) u) (currentW d₁ ε (τ*t) u-1)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hother : 1 ≤ ‖1+W‖ := by
    have hh := norm_sub_norm_le (2:ℂ) (1+W)
    have he : (2:ℂ)-(1+W)=-(W-1) := by ring
    rw [he,norm_neg] at hh
    norm_num at hh
    linarith
  have hdist' : c*(|u|+ε) ≤ ‖1-W‖ := by
    change c*(|u|+ε+1*(τ*t)) ≤ ‖1-W‖ at hdist
    nlinarith [mul_nonneg hc.le hτt]
  have hh := interior_residue_sqrt_majorant W c (|u|+ε) hWim hc
    (by positivity) hdist' hother
  have heW : W = IsingBulk.Branch.dispersion s (plateauY d.c₀ ε τ t d.thetaB u) := by
    simp [W,diskBranchW,d₁,unitDeformationData,plateauY]
  rw [heW] at hh
  convert hh using 1
  ring

end
end IsingBulk.Tail
