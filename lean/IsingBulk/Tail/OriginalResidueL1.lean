import IsingBulk.Tail.OriginalResidueL2
import IsingBulk.Analysis.BranchLength

/-! Uniform L1 control of the literal original residue, retaining both
integrable square-root branch singularities. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology

theorem reciprocal_sqrt_shifted_integral {C eps P b : ℝ}
    (hC : 0 ≤ C) (heps : 0 < eps) (hP : 0 ≤ P) (hb : |b| ≤ P) :
    (∫ θ in -P..P, C/Real.sqrt (|θ-b|+eps)) ≤ 4*C*Real.sqrt (2*P) := by
  let g := fun u : ℝ => C/Real.sqrt (|u|+eps)
  have hg : Continuous g := continuous_const.div (continuous_abs.add continuous_const).sqrt
    (fun u => (Real.sqrt_pos.mpr (by positivity)).ne')
  change (∫ θ in -P..P, g (θ-b)) ≤ _
  rw [intervalIntegral.integral_comp_sub_right]
  apply (intervalIntegral.integral_mono_interval (c := -(2*P)) (d := 2*P)
    (by linarith [abs_le.mp hb]) (by linarith) (by linarith [abs_le.mp hb])
    (Filter.Eventually.of_forall (fun u => by dsimp [g]; positivity))
    (hg.intervalIntegrable _ _)).trans
  exact reciprocal_sqrt_integral eps (2*P) C heps (by positivity) hC

theorem residue_square_majorant_implies_l1 {x C B eps a b : ℝ}
    (_hx : 0 ≤ x) (hC : 0 ≤ C) (hB : 0 ≤ B) (heps : 0 < eps)
    (hs : x^2 ≤ C^2/(|a|+eps)+C^2/(|b|+eps)+B^2) :
    x ≤ C/Real.sqrt (|a|+eps)+C/Real.sqrt (|b|+eps)+B := by
  have ha : 0 ≤ C/Real.sqrt (|a|+eps) := by positivity
  have hb : 0 ≤ C/Real.sqrt (|b|+eps) := by positivity
  have hea : (C/Real.sqrt (|a|+eps))^2=C^2/(|a|+eps) := by rw [div_pow,Real.sq_sqrt (by positivity)]
  have heb : (C/Real.sqrt (|b|+eps))^2=C^2/(|b|+eps) := by rw [div_pow,Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg ha hb,mul_nonneg ha hB,mul_nonneg hb hB]

theorem original_residue_l1_oneperiod (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ A c e : ℝ, 0 < A ∧ 0 < c ∧ 0 < e ∧
      ∀ eps : ℝ, 0 < eps → eps < e → ∀ s : ℂ,
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        Continuous (fun θ : ℝ => ‖residueFactor (globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) θ))‖) ∧
        (∫ θ in Icc (0:ℝ) (2*Real.pi),
          ‖residueFactor (globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) θ))‖) ≤ A := by
  obtain ⟨C,B,c,e,hC,hB,hc,he,_he1,hdata⟩ := original_residue_square_pointwise d hcsmall
  refine ⟨8*C*Real.sqrt (2*Real.pi)+2*Real.pi*B,c,e,by positivity,hc,he,?_⟩
  intro eps heps hepslt s hs
  obtain ⟨hcont,hpoint⟩ := hdata eps heps hepslt s hs
  have hc' : Continuous (fun θ : ℝ => ‖residueFactor (globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) θ))‖) := by
    simpa only [originalResidueAngle,radialAnglePoint_eq_anglePoint_exp] using hcont.norm
  refine ⟨hc',?_⟩
  let f := fun θ : ℝ => C/Real.sqrt (|θ-d.thetaB|+eps)
  let g := fun θ : ℝ => C/Real.sqrt (|θ+d.thetaB|+eps)
  have hf : Continuous f := by
    apply continuous_const.div (((continuous_id.sub continuous_const).abs.add continuous_const).sqrt)
    intro θ
    exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg _) heps)).ne'
  have hg : Continuous g := by
    apply continuous_const.div (((continuous_id.add continuous_const).abs.add continuous_const).sqrt)
    intro θ
    exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (abs_nonneg _) heps)).ne'
  have hmajor : (∫ θ in -Real.pi..Real.pi, ‖originalResidueAngle d eps s θ‖) ≤
      ∫ θ in -Real.pi..Real.pi, f θ+g θ+B := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (hcont.norm.intervalIntegrable _ _) ((hf.add hg |>.add continuous_const).intervalIntegrable _ _)
    intro θ hθ
    exact residue_square_majorant_implies_l1 (norm_nonneg _) hC.le hB.le heps
      (hpoint θ (abs_le.mpr hθ))
  have hfint := reciprocal_sqrt_shifted_integral hC.le heps Real.pi_pos.le
    (by rw [abs_of_pos d.thetaB_pos]; exact d.thetaB_lt.le)
  have hgint := reciprocal_sqrt_shifted_integral hC.le heps Real.pi_pos.le
    (show |-d.thetaB| ≤ Real.pi by rw [abs_neg,abs_of_pos d.thetaB_pos]; exact d.thetaB_lt.le)
  simp only [sub_neg_eq_add] at hgint
  have hsplit : (∫ θ in -Real.pi..Real.pi, f θ+g θ+B) =
      (∫ θ in -Real.pi..Real.pi,f θ)+(∫ θ in -Real.pi..Real.pi,g θ)+2*Real.pi*B := by
    have hspl := intervalIntegral.integral_add ((hf.add hg).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
      ((continuous_const : Continuous (fun _ : ℝ => B)).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
    simp only [Pi.add_apply] at hspl
    rw [hspl,intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const,smul_eq_mul]
    ring
  rw [hsplit] at hmajor
  have hfinal : (∫ θ in -Real.pi..Real.pi, ‖originalResidueAngle d eps s θ‖) ≤
      8*C*Real.sqrt (2*Real.pi)+2*Real.pi*B := by
    change (∫ θ in -Real.pi..Real.pi,f θ) ≤ _ at hfint
    change (∫ θ in -Real.pi..Real.pi,g θ) ≤ _ at hgint
    linarith
  have hp := (originalResidueAngle_periodic d eps s).comp (fun z : ℂ => ‖z‖)
  have heq := hp.intervalIntegral_add_eq 0 (-Real.pi)
  simp only [Function.comp_def,zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] at heq
  rw [← heq] at hfinal
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,← integral_Icc_eq_integral_Ioc] at hfinal
  simpa only [Function.comp_def,originalResidueAngle,radialAnglePoint_eq_anglePoint_exp] using hfinal

end
end IsingBulk.Tail
