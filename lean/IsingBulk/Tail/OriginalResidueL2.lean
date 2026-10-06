import IsingBulk.Tail.OriginalBothBranches
import IsingBulk.Tail.OriginalCompactResidue
import IsingBulk.Tail.ReciprocalDistanceIntegral

/-! Actual whole-original-circle squared residue control. Local estimates
at both branch signs and the true compact complement are combined before
integration; no L2 bound is an external input. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped Topology

def originalResidueAngle (d : LocalBranchData) (e : ℝ) (s : ℂ) (theta : ℝ) : ℂ :=
  residueFactor (globalRoot s (radialAnglePoint (-d.c₀*e) theta))

theorem originalResidueAngle_continuous (d : LocalBranchData) (e : ℝ) (s : ℂ)
    (hW : ∀ theta : ℝ, 0 < (sourceW s (radialAnglePoint (-d.c₀*e) theta)).im) :
    Continuous (originalResidueAngle d e s) := by
  have hy : Continuous (fun theta : ℝ => radialAnglePoint (-d.c₀*e) theta) := by
    unfold radialAnglePoint
    fun_prop
  have hg : Continuous (fun theta : ℝ => globalRoot s (radialAnglePoint (-d.c₀*e) theta)) := by
    apply continuous_iff_continuousAt.mpr
    intro theta
    exact (globalRoot_y_differentiableAt (Complex.exp_ne_zero _) (hW theta)).continuousAt.comp_of_eq
      hy.continuousAt rfl
  have hden (theta : ℝ) : 1-(globalRoot s (radialAnglePoint (-d.c₀*e) theta))^2 ≠ 0 := by
    have hn : ‖globalRoot s (radialAnglePoint (-d.c₀*e) theta)‖ < 1 :=
      interiorRoot_norm_lt_one (hW theta)
    simpa only [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one hn hn
  exact (continuous_const.mul (hg.pow 2)).div (continuous_const.sub (hg.pow 2)) hden

/-- Every angle belongs to one of the two actual branch arcs or the compact
complement; the constants precede epsilon, s and the angular variable. -/
theorem original_residue_square_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C B delta e0 : ℝ, 0 < C ∧ 0 < B ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        Continuous (originalResidueAngle d e s) ∧
        ∀ theta : ℝ, |theta| ≤ Real.pi →
          ‖originalResidueAngle d e s theta‖^2 ≤
            C^2/(|theta-d.thetaB|+e)+C^2/(|theta+d.thetaB|+e)+B^2 := by
  obtain ⟨C,deltaB,hB,eB,hC,hdeltaB,hhB,heB,hbranch⟩ := original_disk_both_branch_onebody d
  let h := min (hB/2) (min (d.thetaB/2) ((Real.pi-d.thetaB)/2))
  have hh : 0 < h := by
    dsimp only [h]
    exact lt_min (half_pos hhB) (lt_min (half_pos d.thetaB_pos) (half_pos (sub_pos.mpr d.thetaB_lt)))
  have hh1 : h < hB := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hhB)
  have hh2 : h < d.thetaB := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    (half_lt_self d.thetaB_pos)
  have hh3 : d.thetaB+h < Real.pi := by
    have hl : h ≤ (Real.pi-d.thetaB)/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith [d.thetaB_lt]
  obtain ⟨B,deltaC,eC,hBc,hdeltaC,heC,hcompact⟩ := original_disk_compact_residue d hcsmall h hh hh2 hh3
  have hsin : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨deltaG,eG,hdeltaG,_,heG,_,hglobal⟩ :=
    original_disk_sourceW_upper d.theta d.c₀ hsin d.c₀_pos hcsmall
  let delta := min deltaB (min deltaC deltaG)
  let e0 := min eB (min eC (min eG 1))
  have hd : 0 < delta := lt_min hdeltaB (lt_min hdeltaC hdeltaG)
  have he0 : 0 < e0 := lt_min heB (lt_min heC (lt_min heG (by norm_num)))
  refine ⟨C,B,delta,e0,hC,hBc,hd,he0,?_,?_⟩
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  · intro e he heSmall s hs
    have heB' : e < eB := heSmall.trans_le (min_le_left _ _)
    have heC' : e < eC := heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have heG' : e < eG := heSmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hsB : ‖s-radialParameter d.theta e‖ ≤ deltaB*e := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) he.le)
    have hsC : ‖s-radialParameter d.theta e‖ ≤ deltaC*e := hs.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) he.le)
    have hsG : ‖s-radialParameter d.theta e‖ ≤ deltaG*e := hs.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) he.le)
    refine ⟨originalResidueAngle_continuous d e s (hglobal e he heG' s hsG),?_⟩
    intro theta htheta
    have hplus : 0 ≤ C^2/(|theta+d.thetaB|+e) := by positivity
    have hminus : 0 ≤ C^2/(|theta-d.thetaB|+e) := by positivity
    by_cases hp : |theta-d.thetaB| < h
    · have hb := (hbranch e (theta-d.thetaB) s he heB' (hp.trans hh1) hsB).2
      have hy : originalUpperPoint d.c₀ e d.thetaB (theta-d.thetaB) =
          radialAnglePoint (-d.c₀*e) theta := by
        unfold originalUpperPoint radialAnglePoint
        congr 1
        push_cast
        ring
      rw [hy] at hb
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [div_pow,Real.sq_sqrt (by positivity)] at hsq
      exact hsq.trans (by nlinarith [sq_nonneg B])
    · by_cases hm : |theta+d.thetaB| < h
      · have hb := (hbranch e (theta+d.thetaB) s he heB' (hm.trans hh1) hsB).1
        have hy : originalLowerPoint d.c₀ e d.thetaB (theta+d.thetaB) =
            radialAnglePoint (-d.c₀*e) theta := by
          unfold originalLowerPoint radialAnglePoint
          congr 1
          push_cast
          ring
        rw [hy] at hb
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
        rw [div_pow,Real.sq_sqrt (by positivity)] at hsq
        exact hsq.trans (by nlinarith [sq_nonneg B])
      · have hsep : h ≤ |(|theta|-d.thetaB)| := by
          by_cases ht : 0 ≤ theta
          · rw [abs_of_nonneg ht]
            exact le_of_not_gt hp
          · rw [abs_of_nonpos (le_of_not_ge ht),show -theta-d.thetaB=-(theta+d.thetaB) by ring,abs_neg]
            exact le_of_not_gt hm
        have hb := hcompact e theta s he heC' htheta hsep hsC
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
        exact hsq.trans (by nlinarith)

theorem square_integral_le_two_branch_logs {P e b C B : ℝ} {R : ℝ → ℂ}
    (hP : 0 ≤ P) (he : 0 < e) (he1 : e ≤ 1) (hb : |b| ≤ P)
    (hR : Continuous R)
    (hbound : ∀ theta : ℝ, |theta| ≤ P →
      ‖R theta‖^2 ≤ C^2/(|theta-b|+e)+C^2/(|theta+b|+e)+B^2) :
    (∫ theta : ℝ in -P..P, ‖R theta‖^2) ≤
      4*C^2*(Real.log (2*P+1)+Real.log (1/e))+2*P*B^2 := by
  have hk (v : ℝ) : Continuous (fun theta : ℝ => (|theta-v|+e)⁻¹) := by
    apply ((continuous_id.sub continuous_const).abs.add continuous_const).inv₀
    intro theta
    exact (add_pos_of_nonneg_of_pos (abs_nonneg _) he).ne'
  have h1 : Continuous (fun theta : ℝ => C^2/(|theta-b|+e)) := by
    convert! ((continuous_const : Continuous (fun _ : ℝ => C^2)).mul (hk b)) using 1
  have h2 : Continuous (fun theta : ℝ => C^2/(|theta+b|+e)) := by
    convert! ((continuous_const : Continuous (fun _ : ℝ => C^2)).mul (hk (-b))) using 1
    funext theta
    simp only [Pi.mul_apply,sub_neg_eq_add,div_eq_mul_inv]
  have hmono : (∫ theta : ℝ in -P..P, ‖R theta‖^2) ≤
      ∫ theta : ℝ in -P..P, (C^2/(|theta-b|+e)+C^2/(|theta+b|+e)+B^2) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      ((hR.norm.pow 2).intervalIntegrable _ _) (((h1.add h2).add continuous_const).intervalIntegrable _ _)
    intro theta htheta
    exact hbound theta (abs_le.mpr htheta)
  have hlog1 := mul_le_mul_of_nonneg_left (reciprocal_shifted_log_bound hP he he1 hb) (sq_nonneg C)
  have hlog2 := mul_le_mul_of_nonneg_left (reciprocal_shifted_log_bound hP he he1
    (show |-b| ≤ P by simpa only [abs_neg] using hb)) (sq_nonneg C)
  simp only [sub_neg_eq_add] at hlog2
  have heq : (∫ theta : ℝ in -P..P, (C^2/(|theta-b|+e)+C^2/(|theta+b|+e)+B^2)) =
      C^2*(∫ theta : ℝ in -P..P, (|theta-b|+e)⁻¹)+
      C^2*(∫ theta : ℝ in -P..P, (|theta+b|+e)⁻¹)+2*P*B^2 := by
    have hsplit := intervalIntegral.integral_add ((h1.add h2).intervalIntegrable (μ := volume) (-P) P)
      ((continuous_const : Continuous (fun _ : ℝ => B^2)).intervalIntegrable (μ := volume) (-P) P)
    simp only [Pi.add_apply] at hsplit
    rw [hsplit,intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
    simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul]
    ring
  rw [heq] at hmono
  nlinarith

/-- Source ultra-high one-body L2 estimate, with one common actual original
complex disk and constants chosen before epsilon and the angular integral. -/
theorem original_residue_l2_logarithmic (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ A delta e0 : ℝ, 0 < A ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        (∫ theta : ℝ in -Real.pi..Real.pi, ‖originalResidueAngle d e s theta‖^2) ≤
          A*(Real.log (1/e)+1) := by
  obtain ⟨C,B,delta,e0,_,_,hd,he0,he01,hdata⟩ := original_residue_square_pointwise d hcsmall
  let A := 4*C^2*(Real.log (2*Real.pi+1)+1)+2*Real.pi*B^2+1
  have hlog : 0 ≤ Real.log (2*Real.pi+1) := Real.log_nonneg (by linarith [Real.pi_pos])
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A,delta,e0,hA,hd,he0,he01,?_⟩
  intro e he heSmall s hs
  obtain ⟨hcont,hbound⟩ := hdata e he heSmall s hs
  have he1 : e ≤ 1 := heSmall.le.trans he01
  have hi := square_integral_le_two_branch_logs Real.pi_pos.le he he1
    (b := d.thetaB) (by rw [abs_of_pos d.thetaB_pos]; exact d.thetaB_lt.le) hcont hbound
  have hH : 0 ≤ Real.log (1/e) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith))
  have hlogmajor : Real.log (2*Real.pi+1)+Real.log (1/e) ≤
      (Real.log (2*Real.pi+1)+1)*(Real.log (1/e)+1) := by
    nlinarith [mul_nonneg hlog hH]
  have hm := mul_le_mul_of_nonneg_left hlogmajor (show 0 ≤ 4*C^2 by positivity)
  have hBmajor : 2*Real.pi*B^2 ≤ (2*Real.pi*B^2)*(Real.log (1/e)+1) := by
    nlinarith [mul_nonneg (show 0 ≤ 2*Real.pi*B^2 by positivity) hH]
  dsimp only [A]
  nlinarith

theorem radialAnglePoint_eq_anglePoint_exp (v theta : ℝ) :
    radialAnglePoint v theta = anglePoint (Real.exp v) theta := by
  simp only [radialAnglePoint,anglePoint,circleMap,zero_add,Complex.exp_add,Complex.ofReal_exp]

theorem originalResidueAngle_periodic (d : LocalBranchData) (e : ℝ) (s : ℂ) :
    Function.Periodic (originalResidueAngle d e s) (2*Real.pi) := by
  intro theta
  simp only [originalResidueAngle,radialAnglePoint_eq_anglePoint_exp,anglePoint]
  rw [periodic_circleMap 0 (Real.exp (-d.c₀*e)) theta]

/-- The same actual L2 estimate on the source's normalized-angle period. -/
theorem original_residue_l2_oneperiod (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ A delta e0 : ℝ, 0 < A ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        (∫ theta in Icc (0:ℝ) (2*Real.pi),
          ‖residueFactor (globalRoot s (anglePoint (Real.exp (-d.c₀*e)) theta))‖^2) ≤
          A*(Real.log (1/e)+1) := by
  obtain ⟨A,delta,e0,hA,hd,he0,he01,hbound⟩ := original_residue_l2_logarithmic d hcsmall
  refine ⟨A,delta,e0,hA,hd,he0,he01,?_⟩
  intro e he heSmall s hs
  have hb := hbound e he heSmall s hs
  have hp := (originalResidueAngle_periodic d e s).comp (fun z : ℂ => ‖z‖^2)
  have heq := hp.intervalIntegral_add_eq 0 (-Real.pi)
  simp only [Function.comp_def,zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] at heq
  rw [← heq] at hb
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,← integral_Icc_eq_integral_Ioc] at hb
  simpa only [Function.comp_def,originalResidueAngle,radialAnglePoint_eq_anglePoint_exp] using hb

end
end IsingBulk.Tail
