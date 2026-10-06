import IsingBulk.Tail.SelectedFDiskOneBody
import IsingBulk.Tail.ProtectedBranchDisk

/-! Actual lower-branch residue control uniformly over the protected current
interval. Occupancy and lambda follow every constant. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

set_option maxHeartbeats 1200000 in
theorem protected_disk_branch_onebody (d : LocalBranchData) :
    ∃ C h r : ℝ, 0 < C ∧ 0 < h ∧ 0 < r ∧ ∀ τ : ℝ, 0 < τ → τ < r →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (eps lamStar lam P u : ℝ) (s : ℂ),
        1 ≤ N → 0 < eps → eps < r → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 → 1 ≤ P → P ≤ N → |u| < h →
        ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
        ‖residueFactor (selectedContinuedRoot s
          (plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u))‖ ≤ C/Real.sqrt (|u|+eps) := by
  let d₁ := unitDeformationData d
  obtain ⟨cM,CM,rM,hcM,_hCM,hrM,hmod⟩ := current_modulus_Q d₁
  obtain ⟨b,CI,rI,hb,_hCI,hrI,him⟩ := current_imaginary_margin d₁
  have hcont : ContinuousAt (fun z : ℝ × ℝ × ℝ => ‖currentW d₁ z.1 z.2.1 z.2.2-1‖) 0 :=
    ((currentW_continuous d₁).sub continuousAt_const).norm
  have hzero : ‖currentW d₁ 0 0 0-1‖ < 1/4 := by rw [currentW_zero]; norm_num
  obtain ⟨rn,hrn,hn⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_lt continuousAt_const hzero)
  let h := min rM (min rI rn)
  let r := min h 1
  have hh : 0 < h := lt_min hrM (lt_min hrI hrn)
  have hr : 0 < r := lt_min hh zero_lt_one
  have hhM : h ≤ rM := min_le_left _ _
  have hhI : h ≤ rI := (min_le_right _ _).trans (min_le_left _ _)
  have hhn : h ≤ rn := (min_le_right _ _).trans (min_le_right _ _)
  have hrh : r ≤ h := min_le_left _ _
  let κ := min cM b
  have hκ : 0 < κ := lt_min hcM hb
  have hκM : κ ≤ cM := min_le_left _ _
  have hκb : κ ≤ b := min_le_right _ _
  refine ⟨1/Real.sqrt cM,h,r,by positivity,hh,hr,?_⟩
  intro τ hτ hτr
  let c := min (1/12:ℝ) (κ*τ/12)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1/12 := min_le_left _ _
  have hcκ : c ≤ κ*τ/12 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro N eps lamStar lam P u s hN heps hepsr hls hl hl1 hP hPN hu hsd
  have hnN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let t := lam*P/(N:ℝ)
  have hlam : 0 ≤ lam := hls.le.trans hl
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    apply (div_le_one hn0).mpr
    nlinarith
  have hτt : 0 ≤ τ*t := mul_nonneg hτ.le ht
  have hτtr : τ*t < r := (mul_le_of_le_one_right hτ.le ht1).trans_lt hτr
  have hrad : c*lamStar/(N:ℝ)^2 ≤ c*t :=
    (protected_radius_le hN hc.le hls.le hl hP).trans (div_le_self (by positivity) hnN)
  have hradius : c*lamStar/(N:ℝ)^2 ≤ c :=
    hrad.trans (mul_le_of_le_one_right hc.le ht1)
  have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
    linarith only [hsd,hradius,hc1]
  have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
  have hsn := norm_ge_half_of_near_unit hnorm hsmall
  let W₀ := currentW d₁ eps (τ*t) u
  let W := sourceW s (plateauY d.c₀ eps τ t d.thetaB u)
  have hW₀eq : W₀=sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) := by
    dsimp only [W₀]
    rw [currentW_dispersion]
    simp only [d₁,unitDeformationData,plateauY,one_mul]
    rfl
  have hdiff : ‖W-W₀‖ ≤ 3*c*lamStar/(N:ℝ)^2 := by
    rw [hW₀eq]
    have he : W-sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) =
        sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,sourceW]; ring
    rw [he]
    calc
      _ ≤ 3*‖s-radialParameter d.theta eps‖ := sourceS_sub_norm_le hsn hnorm
      _ ≤ 3*(c*lamStar/(N:ℝ)^2) := mul_le_mul_of_nonneg_left hsd (by norm_num)
      _ = _ := by ring
  have hmove : ‖W-W₀‖ ≤ κ*τ*t/4 := by
    have hct := mul_le_mul_of_nonneg_right hcκ ht
    have hrad3 := mul_le_mul_of_nonneg_left hrad (by norm_num : (0:ℝ)≤3)
    have he : 3*(c*lamStar/(N:ℝ)^2)=3*c*lamStar/(N:ℝ)^2 := by ring
    rw [he] at hrad3
    nlinarith only [hdiff,hrad3,hct]
  have hdist0 := (hmod eps (τ*t) u heps (hepsr.trans_le (hrh.trans hhM)) hτt
    (hτtr.trans_le (hrh.trans hhM)) (hu.trans_le hhM)).1
  have him0 := (him eps (τ*t) u heps (hepsr.trans_le (hrh.trans hhI)) hτt
    (hτtr.trans_le (hrh.trans hhI)) (hu.trans_le hhI)).1
  change cM*(|u|+eps+1*(τ*t)) ≤ ‖1-W₀‖ at hdist0
  change b*(eps+1*(τ*t)) ≤ W₀.im at him0
  have hκMt := mul_le_mul_of_nonneg_right hκM hτt
  have hκbt := mul_le_mul_of_nonneg_right hκb hτt
  have hdist : cM*(|u|+eps) ≤ ‖1-W‖ := by
    have htri := norm_sub_norm_le (1-W₀) (1-W)
    have he : (1-W₀)-(1-W)=W-W₀ := by ring
    rw [he] at htri
    nlinarith only [hdist0,htri,hmove,hκMt,mul_nonneg hcM.le hτt]
  have hWi : 0 < W.im := by
    have himove := Complex.abs_im_le_norm (W-W₀)
    simp only [Complex.sub_im] at himove
    have hleft := (abs_le.mp (himove.trans hmove)).1
    nlinarith only [him0,hleft,hκbt,mul_pos hb heps,mul_nonneg hb.le hτt]
  have hnear : ‖W₀-1‖ < 1/4 := by
    apply hn (y := (eps,τ*t,u))
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos heps,abs_of_nonneg hτt,abs_of_nonneg hτ.le,abs_of_nonneg ht]
      using And.intro (hepsr.trans_le (hrh.trans hhn))
        (And.intro (hτtr.trans_le (hrh.trans hhn)) (hu.trans_le hhn))
  have hmoveSmall : ‖W-W₀‖ ≤ 1/4 := by
    have hh' : 3*c*lamStar/(N:ℝ)^2 ≤ 3*c := by
      have hh := mul_le_mul_of_nonneg_left hradius (by norm_num : (0:ℝ)≤3)
      simpa only [mul_div_assoc,mul_assoc] using hh
    linarith only [hdiff,hh',hc1]
  have hWnear : ‖W-1‖ < 1/2 := by
    have htri := norm_add_le (W-W₀) (W₀-1)
    rw [sub_add_sub_cancel] at htri
    linarith only [htri,hmoveSmall,hnear]
  have hother : 1 ≤ ‖1+W‖ := by
    have htri := norm_sub_norm_le (2:ℂ) (1+W)
    have he : (2:ℂ)-(1+W)=-(W-1) := by ring
    rw [he,norm_neg] at htri
    norm_num at htri
    linarith only [htri,hWnear]
  have hres := interior_residue_sqrt_majorant W cM (|u|+eps) hWi hcM (by positivity) hdist hother
  change ‖residueFactor (continuedRoot W)‖ ≤ _
  rw [continuedRoot_eq_interiorRoot hWi]
  convert hres using 1
  ring


end
end IsingBulk.Tail
