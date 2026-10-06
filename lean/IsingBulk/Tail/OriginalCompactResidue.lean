import IsingBulk.Tail.OriginalGlobalDisk
import IsingBulk.Tail.LimitingAngularMargins
import IsingBulk.Tail.BranchOneBody

/-! Actual compact-complement residue bound on the same original cε disk.
The angular complement excludes both branch signs explicitly. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem interior_residue_two_gaps (W : ℂ) (a : ℝ) (ha : 0 < a)
    (hi : 0 < W.im) (hminus : a ≤ ‖W-1‖) (hplus : a ≤ ‖W+1‖) :
    ‖residueFactor (interiorRoot W)‖ ≤ 1/a := by
  have he := interior_residue_norm_identity W hi
  have hn := interiorRoot_norm_lt_one hi
  have hprod : a^2 ≤ ‖W^2-1‖ := by
    rw [show W^2-1=(W-1)*(W+1) by ring,norm_mul,pow_two]
    exact mul_le_mul hminus hplus ha.le (norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hprod (sq_nonneg ‖residueFactor (interiorRoot W)‖)
  have hb : (‖residueFactor (interiorRoot W)‖*a)^2 ≤ 1 := by
    rw [mul_pow]
    nlinarith [norm_nonneg (interiorRoot W)]
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (‖residueFactor (interiorRoot W)‖*a-1)]

theorem original_disk_compact_residue (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (h : ℝ)
    (hh : 0 < h) (hhb : h < d.thetaB) (hhπ : d.thetaB+h < Real.pi) :
    ∃ B δ ε₀ : ℝ, 0 < B ∧ 0 < δ ∧ 0 < ε₀ ∧
    ∀ ε θ : ℝ, ∀ s : ℂ, 0 < ε → ε < ε₀ → |θ| ≤ Real.pi →
      h ≤ |(|θ|-d.thetaB)| → ‖s-radialParameter d.theta ε‖ ≤ δ*ε →
      ‖residueFactor (globalRoot s (radialAnglePoint (-d.c₀*ε) θ))‖ ≤ B := by
  have hsin : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  have hc₀ := d.c₀_pos
  obtain ⟨μ,hμ,_,hmargin⟩ := limiting_angular_nonbranch_margins d.thetaB h
    d.thetaB_pos d.thetaB_lt hh hhb hhπ
  obtain ⟨δ,eg,hδ,hδ1,heg,_,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsin hc₀ hcsmall
  let K := 6+2*d.c₀
  have hK : 0 < K := by dsimp [K]; positivity
  let ε₀ := min eg (min (1/4) (min (μ/(2*K)) (1/d.c₀)))
  have he0 : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hes : ε₀ ≤ eg ∧ ε₀ ≤ 1/4 ∧ ε₀ ≤ μ/(2*K) ∧ ε₀ ≤ 1/d.c₀ := by
    have he : ε₀ ≤ min eg (min (1/4) (min (μ/(2*K)) (1/d.c₀))) := le_rfl
    simpa only [le_min_iff] using he
  refine ⟨1/(μ/2),δ,ε₀,by positivity,hδ,he0,?_⟩
  intro ε θ s hε he hθ hsep hs
  have hequarter : ε ≤ 1/4 := he.le.trans hes.2.1
  have ht : 1 ≤ ‖radialParameter d.theta ε‖ := by rw [radialParameter_norm hε.le]; linarith
  have hsn : 1/2 ≤ ‖s‖ := norm_ge_half_of_near_unit ht (by nlinarith)
  have htrace := sourceS_sub_norm_le hsn ht
  have hcenter := sourceS_radial_to_boundary d ε hε.le
  let S : ℂ := ((1+Real.cos d.thetaB:ℝ):ℂ)
  have hS : ‖sourceS s-S‖ ≤ 6*ε := by
    have hx := norm_sub_le_norm_sub_add_norm_sub (sourceS s)
      (sourceS (radialParameter d.theta ε)) S
    nlinarith
  have hv : |-d.c₀*ε| ≤ 1 := by
    rw [abs_mul,abs_neg,abs_of_pos hc₀,abs_of_pos hε]
    have he' := (le_div_iff₀ hc₀).mp (he.le.trans hes.2.2.2)
    nlinarith
  let W := sourceW s (radialAnglePoint (-d.c₀*ε) θ)
  let w₀ := limitingAngularW d.thetaB θ
  have hdiff : ‖W-(w₀:ℂ)‖ ≤ μ/2 := by
    have hx := radial_sourceW_transfer s (1+Real.cos d.thetaB) (-d.c₀*ε) θ hv
    change ‖W-(w₀:ℂ)‖ ≤ ‖sourceS s-S‖+2*|-d.c₀*ε| at hx
    rw [abs_mul,abs_neg,abs_of_pos hc₀,abs_of_pos hε] at hx
    have he' := (le_div_iff₀ (show 0 < 2*K by positivity)).mp (he.le.trans hes.2.2.1)
    dsimp [K] at he'
    nlinarith
  have hi : 0 < W.im := hupper ε hε (he.trans_le hes.1) s hs θ
  obtain ⟨hmplus,_,hmminus⟩ := hmargin θ hθ
  have hminus : μ/2 ≤ ‖W-1‖ := by
    have hn := norm_sub_norm_le ((w₀:ℂ)-1) (W-1)
    have heq : ((w₀:ℂ)-1)-(W-1)=-(W-(w₀:ℂ)) := by ring
    rw [heq,norm_neg] at hn
    have hw : ‖(w₀:ℂ)-1‖=|w₀-1| := by
      rw [show (w₀:ℂ)-1=((w₀-1:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs]
    rw [hw] at hn
    have hm := hmminus hsep
    change μ ≤ |w₀-1| at hm
    linarith
  have hplus : μ/2 ≤ ‖W+1‖ := by
    have hn := Complex.abs_re_le_norm (W-(w₀:ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re] at hn
    have ha := neg_le_abs (W.re-w₀)
    have hr := Complex.re_le_norm (W+1)
    simp only [Complex.add_re,Complex.one_re] at hr
    change μ ≤ w₀+1 at hmplus
    linarith
  exact interior_residue_two_gaps W (μ/2) (by positivity) hi hminus hplus

end
end IsingBulk.Tail
