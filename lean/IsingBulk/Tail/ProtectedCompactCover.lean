import IsingBulk.Tail.DeformedRadialTransfer
import IsingBulk.Tail.LimitingAngularMargins
import IsingBulk.Tail.CompactRootContinuation

/-! A constructed compact continuation cover for actual nonbranch deformed
angles. Angular branch exclusion is explicit, as required by the source
partition; the root cover is a conclusion rather than a setup field. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric

def protectedCompactRegion (d : ℝ) : Set ℂ :=
  {W | 0 ≤ W.im ∧ -1+d ≤ W.re ∧ d ≤ ‖W-1‖ ∧ ‖W‖ ≤ 4}

theorem protectedCompactRegion_isCompact (d : ℝ) : IsCompact (protectedCompactRegion d) := by
  have hc : IsClosed (protectedCompactRegion d) := by
    unfold protectedCompactRegion
    simp only [ofPred_and]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
          (isClosed_le continuous_norm continuous_const)))
  apply (isCompact_closedBall (0:ℂ) 4).of_isClosed_subset hc
  intro W hW
  simpa only [mem_closedBall,dist_zero_right] using hW.2.2.2

theorem protectedCompactRegion_subset_domain {d : ℝ} (hd : 0 < d) :
    protectedCompactRegion d ⊆ continuedRootDomain := by
  intro W hW
  by_cases hi : 0 < W.im
  · exact Or.inl (Or.inl hi)
  have him : W.im=0 := by linarith [hW.1]
  by_cases hr : 1 < W.re
  · exact Or.inl (Or.inr hr)
  right
  have hne : W.re ≠ 1 := by
    intro he
    have hwe : W=1 := Complex.ext he (by simpa using him)
    have hgap := hW.2.2.1
    rw [hwe,sub_self,norm_zero] at hgap
    linarith
  exact abs_lt.mpr ⟨by linarith [hW.2.1],lt_of_le_of_ne (le_of_not_gt hr) hne⟩

theorem protectedCompactRegion_of_near_real {d w : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hwlo : d ≤ w+1) (hwabs : |w| ≤ 3) (hwgap : d ≤ |w-1|) {W : ℂ}
    (hWi : 0 ≤ W.im) (hdiff : ‖W-(w:ℂ)‖ ≤ d/4) :
    W ∈ protectedCompactRegion (d/2) := by
  have hreal := Complex.abs_re_le_norm (W-(w:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hreal
  have hre := (abs_le.mp (hreal.trans hdiff)).1
  have hnorm := norm_sub_norm_le W (w:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs] at hnorm
  have hgap := norm_sub_norm_le ((w:ℂ)-1) (W-1)
  rw [show ((w:ℂ)-1)-(W-1)=(w:ℂ)-W by ring,norm_sub_rev (w:ℂ) W] at hgap
  have hwreal : ‖(w:ℂ)-1‖=|w-1| := by norm_cast
  rw [hwreal] at hgap
  exact ⟨hWi,by linarith,by linarith,by linarith⟩

/-- Constants depend only on the fixed source point and explicit angular
nonbranch margin. They precede all bump functions, dimensions, occupancies,
epsilon, deformation, lambda and angles in the stated box. -/
theorem deformed_nonbranch_compact_cover (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {h : ℝ} (hh : 0 < h)
    (hhb : h < d.thetaB) (hhπ : d.thetaB+h < Real.pi) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ continuedRootDomain ∧
      ∃ r : ℝ, 0 < r ∧ ∀ (N : ℕ), 0 < N → ∀ (f : SelectorFunctions)
      (eps τ lam : ℝ) (θ : Fin N → ℝ),
      0 < eps → eps < r → 0 ≤ τ → τ < r → 0 ≤ lam → lam ≤ 1 →
      (∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) → (∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1) →
      (∀ x, Real.sin x ≤ 0 → f.p x=0) → (∀ x, 0 ≤ Real.sin x → f.m x=0) →
      ∀ i : Fin N, |θ i| ≤ Real.pi → h ≤ |(|θ i|-d.thetaB)| →
      sourceW (radialParameter d.theta eps)
        (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i) ∈ K := by
  obtain ⟨g,hg,hg1,hmargin⟩ := limiting_angular_nonbranch_margins d.thetaB h
    d.thetaB_pos d.thetaB_lt hh hhb hhπ
  have hsin : 0 < Real.sin d.theta :=
    Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by have := d.theta_lt; linarith [Real.pi_pos])
  obtain ⟨δ,e,hδ,_,he,_,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsin d.c₀_pos hcsmall
  let r := min e (min (g/(8*(7+2*d.c₀))) (1/(2*(d.c₀+2))))
  have hc₀ := d.c₀_pos
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨protectedCompactRegion (g/2),protectedCompactRegion_isCompact _,
    protectedCompactRegion_subset_domain (half_pos hg),r,hr,?_⟩
  intro N hN f eps τ lam θ heps hepsr hτ hτr hl0 hl1 hp hm hps hms i hθ hsep
  have hre : r ≤ e := min_le_left _ _
  have hrg : r ≤ g/(8*(7+2*d.c₀)) := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1/(2*(d.c₀+2)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : d.c₀*eps+2*τ ≤ 1 := by
    have hdpos := d.c₀_pos
    have hh := (le_div_iff₀ (show 0 < 2*(d.c₀+2) by positivity)).mp hr1
    nlinarith
  have herror : (3+2*d.c₀)*eps+4*τ ≤ g/4 := by
    have hdpos := d.c₀_pos
    have hh := (le_div_iff₀ (show 0 < 8*(7+2*d.c₀) by positivity)).mp hrg
    nlinarith
  have htrans := deformedPoint_sourceW_transfer d hN f θ heps.le hτ hl0 hl1 hp hm hsmall i
  obtain ⟨hwlo,hwabs,hwsep⟩ := hmargin (θ i) hθ
  have hu0 : 0 < (sourceW (radialParameter d.theta eps)
      (deformedPoint f (Real.exp (-d.c₀*eps)) τ 0 θ i)).im := by
    rw [deformedPoint_polar f (Real.exp_pos _) τ 0 θ i,Real.log_exp]
    simpa only [zero_mul,add_zero,radialAnglePoint] using
      hupper eps heps (hepsr.trans_le hre) (radialParameter d.theta eps)
        (by simp; positivity) (θ i)
  have hu := hu0.trans_le (deformed_sourceW_im_ge hN f (Real.exp_pos _) hτ hl0 θ
    (radialParameter d.theta eps) (fun x => (hp x).1) (fun x => (hm x).1) hps hms i)
  exact protectedCompactRegion_of_near_real hg hg1 hwlo hwabs (hwsep hsep) hu.le (htrans.trans herror)

end
end IsingBulk.Tail
