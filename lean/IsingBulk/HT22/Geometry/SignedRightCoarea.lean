import IsingBulk.HT22.Geometry.SignedExtremeIntegral
import IsingBulk.HT22.Geometry.SignedNegativeCoarea

/-! Both signed full right fibers. The unique crossing θ_min+b=0 is
geometric, and no assertion about smooth-cutoff components is used. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory IsingBulk.Preferred22

set_option maxHeartbeats 1200000 in
/-- The literal full right-rectangle extreme integral. The single crossing
is fixed by the affine constrained minimum; no smooth-cutoff component count
or frozen occupancy hypothesis enters this estimate. -/
theorem signed_right_extreme_integral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ η : ℝ, ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N, ∀ x y r T : ℝ,
      x ≤ y → 0 < r → r ≤ T →
      (∀ t ∈ Icc x y,
        (∀ v, extremeAnglePath θ i j t v ∈ Icc (-d.b-δB) B.delta) ∧
        (∀ v, extremeAnglePath θ i j t i ≤ extremeAnglePath θ i j t v ∧
          extremeAnglePath θ i j t v ≤ extremeAnglePath θ i j t j) ∧
        r ≤ extremeAnglePath θ i j t j-extremeAnglePath θ i j t i ∧
        extremeAnglePath θ i j t j+d.b+ε ≤ T) →
      (∫ t : ℝ in x..y,
        preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
          ‖1-signedActualZ η d B ε τ (extremeAnglePath θ i j t)‖) ≤
        C*(N:ℝ)*Real.sqrt T/r*(1+|Real.log ε|) := by
  obtain ⟨Cn,εn,τn,δB,hCn,hεn,hτn,hδB,hδBδ,hn⟩ := signed_negative_extreme_integral d B
  obtain ⟨Cp,εp,τp,hCp,hεp,hτp,hp⟩ := signed_nonnegative_extreme_integral d B
  obtain ⟨ca,Ca,hca,_,hphase⟩ := preferred_actual_phase_control d B
  let ε₀ := min 1 (min εn εp)
  let τ₀ := min 1 (min τn τp)
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) (lt_min hεn hεp)
  have hτ₀ : 0 < τ₀ := lt_min (by norm_num) (lt_min hτn hτp)
  refine ⟨Cn+Cp,ε₀,τ₀,δB,by positivity,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro η N hN ε τ hε hεr hτ hτr θ i j x y r T hxy hr hrT hgeom
  have hT : 0 < T := hr.trans_le hrT
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_left _ _)).le
  have hτ1 : τ ≤ 1 := (hτr.trans_le (min_le_left _ _)).le
  have hεn' : ε < εn := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεp' : ε < εp := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτn' : τ < τn := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτp' : τ < τp := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hij : i ≠ j := by
    intro he
    have hh := (hgeom x (left_mem_Icc.mpr hxy)).2.2.1
    rw [he,sub_self] at hh
    linarith
  have hei (t : ℝ) : extremeAnglePath θ i j t i+d.b = θ i+d.b+t := by
    simp only [extremeAnglePath,ite_true,ite_eq_right hij]
    ring
  let z := -(θ i+d.b)
  let F := fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
    ‖1-signedActualZ η d B ε τ (extremeAnglePath θ i j t)‖
  let W := Real.sqrt T/r*(1+|Real.log ε|)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hneg (a b : ℝ) (hab : a ≤ b) (hxa : x ≤ a) (hby : b ≤ y) (hbz : b ≤ z) :
      (∫ t : ℝ in a..b, F t) ≤ Cn*(N:ℝ)*W := by
    have hh := hn η N hN ε τ hε hεn' hτ hτn' θ i j a b r T hab hr hrT (by
      intro t ht
      have htx : t ∈ Icc x y := ⟨hxa.trans ht.1,ht.2.trans hby⟩
      have hg := hgeom t htx
      refine ⟨hg.1,?_,hg.2.2.1⟩
      rw [hei]
      dsimp [z] at hbz
      linarith [ht.2])
    calc
      (∫ t : ℝ in a..b, F t) ≤ Cn*W := by simpa only [F,W,mul_div_assoc,mul_assoc] using hh
      _ ≤ Cn*(N:ℝ)*W := by
        have hh := mul_le_mul_of_nonneg_right hN1 (mul_nonneg hCn.le hW)
        nlinarith only [hh]
  have hpos (a b : ℝ) (hab : a ≤ b) (hxa : x ≤ a) (hby : b ≤ y) (hza : z ≤ a) :
      (∫ t : ℝ in a..b, F t) ≤ Cp*(N:ℝ)*W := by
    have hh := hp η N hN ε τ hε hεp' hτ hτp' θ i j a b r T hab hr hT (by
      intro t ht
      have htx : t ∈ Icc x y := ⟨hxa.trans ht.1,ht.2.trans hby⟩
      have hg := hgeom t htx
      have hmin : 0 ≤ extremeAnglePath θ i j t i+d.b := by
        rw [hei]
        dsimp [z] at hza
        linarith [ht.1]
      refine ⟨?_,hg.2⟩
      intro v
      exact ⟨by linarith [(hg.2.1 v).1],(hg.1 v).2⟩)
    simpa only [F,W,mul_div_assoc,mul_assoc] using hh
  have hfinish (h : (∫ t : ℝ in x..y, F t) ≤ (Cn+Cp)*(N:ℝ)*W) :
      (∫ t : ℝ in x..y, F t) ≤ (Cn+Cp)*(N:ℝ)*Real.sqrt T/r*(1+|Real.log ε|) := by
    simpa only [W,mul_div_assoc,mul_assoc] using h
  apply hfinish
  by_cases hyz : y ≤ z
  · have hh := hneg x y hxy le_rfl le_rfl hyz
    have hrest : 0 ≤ Cp*(N:ℝ)*W := by positivity
    nlinarith only [hh,hrest]
  by_cases hzx : z ≤ x
  · have hh := hpos x y hxy le_rfl le_rfl hzx
    have hrest : 0 ≤ Cn*(N:ℝ)*W := by positivity
    nlinarith only [hh,hrest]
  have hxz : x ≤ z := (lt_of_not_ge hzx).le
  have hzy : z ≤ y := (lt_of_not_ge hyz).le
  have hnz := hneg x z hxz le_rfl hzy le_rfl
  have hpz := hpos z y hzy hxz le_rfl le_rfl
  have hnum : Continuous (fun t : ℝ =>
      preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j) :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hG : Continuous (fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)) :=
    (preferred_extreme_phase_smooth d B hε hτ θ i j).continuous
  have hZ : Continuous (fun t : ℝ => signedActualZ η d B ε τ (extremeAnglePath θ i j t)) := by
    simp_rw [signedActualZ_eq_exp η d B hε hτ]
    fun_prop
  have hden (t : ℝ) : ‖1-signedActualZ η d B ε τ (extremeAnglePath θ i j t)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rw [signedActualZ_eq_exp η d B hε hτ]
    apply preferred_phase_denominator_ne_zero
    have hh := (hphase N hN ε τ hε hε1 hτ hτ1 (extremeAnglePath θ i j t)).1
    have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
    simp only [Complex.add_im,Complex.ofReal_im,add_zero]
    nlinarith only [hh,mul_pos (mul_pos hca hNp) hε]
  have hF : Continuous F := hnum.div ((continuous_const.sub hZ).norm) hden
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable x z) (hF.intervalIntegrable z y)
  linarith


end
end IsingBulk.HT22.Geometry
