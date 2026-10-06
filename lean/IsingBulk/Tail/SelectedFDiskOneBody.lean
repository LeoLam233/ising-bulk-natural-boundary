import IsingBulk.Tail.BranchOneBody
import IsingBulk.Tail.BranchDiskPerturbation
import IsingBulk.Tail.SelectedFContinuation

/-! Integrable one-body control on the enlarged selected c/N disk. Unlike a
pointwise sqrt(N) estimate, the conclusion is independent of the coupled P/N
and can be integrated in the actual angular variables. Angular width is
fixed separately from later parameter-radius choices. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

set_option maxHeartbeats 1200000 in
theorem selected_disk_branch_onebody (d : LocalBranchData) :
    ∃ C h r : ℝ, 0 < C ∧ 0 < h ∧ 0 < r ∧ ∀ τ : ℝ, 0 < τ → τ < r →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (eps P u : ℝ) (s : ℂ),
        1 ≤ N → 0 < eps → eps < r → 1 ≤ P → P ≤ N → |u| < h →
        ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
        ‖residueFactor (selectedContinuedRoot s
          (plateauY d.c₀ eps τ (P/(N:ℝ)) d.thetaB u))‖ ≤ C/Real.sqrt (|u|+eps) := by
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
  intro N eps P u s hN heps hepsr hP hPN hu hsd
  have hnN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let t := P/(N:ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one hn0).mpr hPN
  have hτt : 0 ≤ τ*t := mul_nonneg hτ.le ht
  have hτtr : τ*t < r := (mul_le_of_le_one_right hτ.le ht1).trans_lt hτr
  have hrad : c/(N:ℝ) ≤ c*t := by
    dsimp [t]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith only [hc,hP]) hn0.le
  have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
    have hrad' : c/(N:ℝ) ≤ c := div_le_self hc.le hnN
    linarith only [hsd,hrad',hc1]
  have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
  have hsn := norm_ge_half_of_near_unit hnorm hsmall
  let W₀ := currentW d₁ eps (τ*t) u
  let W := sourceW s (plateauY d.c₀ eps τ t d.thetaB u)
  have hW₀eq : W₀=sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) := by
    dsimp only [W₀]
    rw [currentW_dispersion]
    simp only [d₁,unitDeformationData,plateauY,one_mul]
    rfl
  have hdiff : ‖W-W₀‖ ≤ 3*c/(N:ℝ) := by
    rw [hW₀eq]
    have he : W-sourceW (radialParameter d.theta eps) (plateauY d.c₀ eps τ t d.thetaB u) =
        sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,sourceW]; ring
    rw [he]
    calc
      _ ≤ 3*‖s-radialParameter d.theta eps‖ := sourceS_sub_norm_le hsn hnorm
      _ ≤ 3*(c/(N:ℝ)) := mul_le_mul_of_nonneg_left hsd (by norm_num)
      _ = _ := by ring
  have hmove : ‖W-W₀‖ ≤ κ*τ*t/4 := by
    have hct := mul_le_mul_of_nonneg_right hcκ ht
    have hrad3 := mul_le_mul_of_nonneg_left hrad (by norm_num : (0:ℝ)≤3)
    have he : 3*(c/(N:ℝ))=3*c/(N:ℝ) := by ring
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
    have hh' : 3*c/(N:ℝ) ≤ 3*c := div_le_self (by positivity) hnN
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

/-- Compact continued roots have uniformly bounded one-body residues and
inverses on a constructed complex tube. No unit-disk assertion is used. -/
theorem continuedRoot_compact_onebody {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ continuedRootDomain) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ W₀ ∈ K, ∀ W : ℂ, ‖W-W₀‖ ≤ c →
      ‖residueFactor (continuedRoot W)‖ ≤ C ∧ ‖(continuedRoot W)⁻¹‖ ≤ C := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open continuedRootDomain_isOpen hKD
  obtain ⟨r',hr',hcompact⟩ := hK.exists_isCompact_cthickening
  let c := min r r'
  let K' := Metric.cthickening c K
  have hc : 0 < c := lt_min hr hr'
  have hK'D : K' ⊆ continuedRootDomain :=
    (Metric.cthickening_mono (min_le_left r r') K).trans hsub
  have hK' : IsCompact K' :=
    hcompact.of_isClosed_subset Metric.isClosed_cthickening (Metric.cthickening_mono (min_le_right r r') K)
  have hres : ContinuousOn (fun W : ℂ => residueFactor (continuedRoot W)) K' := by
    intro W hW
    have hcW := (continuedRoot_analyticAt (hK'D hW)).continuousAt
    exact (((continuousAt_const.mul (hcW.pow 2)).div
      (continuousAt_const.sub (hcW.pow 2)) (continuedRoot_residue_gap (hK'D hW)))).continuousWithinAt
  have hinv : ContinuousOn (fun W : ℂ => (continuedRoot W)⁻¹) K' := by
    intro W hW
    exact ((continuedRoot_analyticAt (hK'D hW)).continuousAt.inv₀ (continuedRoot_nonzero W)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK'.exists_bound_of_continuousOn hres
  obtain ⟨B,hB⟩ := hK'.exists_bound_of_continuousOn hinv
  let C := max (max M B) 0+1
  have hC : 0 < C := by dsimp [C]; have hh := le_max_right (max M B) 0; linarith
  have hMC : M ≤ C := (le_max_left M B).trans ((le_max_left (max M B) 0).trans (by dsimp [C]; linarith))
  have hBC : B ≤ C := (le_max_right M B).trans ((le_max_left (max M B) 0).trans (by dsimp [C]; linarith))
  refine ⟨c,C,hc,hC,?_⟩
  intro W₀ hW₀ W hW
  have hmem : W ∈ K' := Metric.mem_cthickening_of_dist_le W W₀ c K hW₀
    (by simpa only [dist_eq_norm] using hW)
  exact ⟨(hM W hmem).trans hMC,(hB W hmem).trans hBC⟩

end
end IsingBulk.Tail
