import IsingBulk.Tail.MicrocoreTransport
import IsingBulk.Tail.RegularPairNeighborhood
import IsingBulk.First.GlobalRootChartBridge
import IsingBulk.Tail.SelectorDefinitions

/-! Literal source one-body and complete-pair factors in regular microcore
coordinates, retaining the normalized angular measure. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets

 theorem complex_phase_one_sub_sq (φ : ℂ) :
    1-(Complex.exp (-Complex.I*φ))^2 =
      2*Complex.I*Complex.sin φ*Complex.exp (-Complex.I*φ) := by
  have he : Complex.exp (φ*Complex.I)*Complex.exp (-φ*Complex.I)=1 := by
    rw [← Complex.exp_add]
    simp
  have hd : Complex.exp (φ*Complex.I)-Complex.exp (-φ*Complex.I)=2*Complex.I*Complex.sin φ := by
    simp only [Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
    ring
  have hm := congrArg (fun z : ℂ => z*Complex.exp (-φ*Complex.I)) hd
  rw [sub_mul,he] at hm
  have hx : -Complex.I*φ=-φ*Complex.I := by ring
  rw [hx]
  linear_combination hm

 theorem complex_phase_residue_value (φ : ℂ) :
    residueFactor (Complex.exp (-Complex.I*φ)) =
      Complex.exp (-Complex.I*φ)/(Complex.I*Complex.sin φ) := by
  unfold residueFactor
  rw [complex_phase_one_sub_sq]
  field_simp

 def microRegularOneBody (s φ : ℂ) : ℂ :=
  -Complex.exp (-Complex.I*φ)/((Real.pi:ℂ)*(1-(regularY s φ)^(-2:ℤ)))

 theorem angular_regular_measure_identity (y φ : ℂ) (hy : y ≠ 0)
    (hd : 1-y^(-2:ℤ) ≠ 0) (hn : Complex.sin φ ≠ 0) :
    (Complex.I*(y-y⁻¹)/2/Complex.sin φ)*
      (-Complex.exp (-Complex.I*φ)/((Real.pi:ℂ)*(1-y^(-2:ℤ)))) =
      residueFactor (Complex.exp (-Complex.I*φ))*y/(2*(Real.pi:ℂ)) := by
  rw [complex_phase_residue_value]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [zpow_neg,zpow_ofNat] at hd ⊢
  have hysq : y^2-1 ≠ 0 := by
    intro he
    have hs : y^2=1 := sub_eq_zero.mp he
    simp [hs] at hd
  field_simp [hy,hn,hpi,hysq]
  simp [Complex.I_sq]

 theorem micro_regular_onebody_pullback (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re)
    (hd : 1-(angularY v θ u)^(-2:ℤ) ≠ 0)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    chartB s v θ u*microRegularOneBody s (chartPhase s v θ u) =
      residueFactor (Complex.exp (-Complex.I*chartPhase s v θ u))*angularY v θ u/(2*(Real.pi:ℂ)) := by
  unfold microRegularOneBody
  rw [regularY_chartPhase s v θ u hg]
  exact angular_regular_measure_identity _ _ (Complex.exp_ne_zero _) hd hn

 theorem chart_root_eq_physical (s : ℂ) (v θ : ℝ) (u : ℂ) :
    globalRoot s (angularY v θ u)=Complex.exp (-Complex.I*chartPhase s v θ u) := by
  rw [globalRoot_eq_exp_lowerArccos]
  rfl

 theorem micro_regular_onebody_source (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re)
    (hd : 1-(angularY v θ u)^(-2:ℤ) ≠ 0)
    (hn : Complex.sin (chartPhase s v θ u) ≠ 0) :
    chartB s v θ u*microRegularOneBody s (chartPhase s v θ u) =
      residueFactor (globalRoot s (angularY v θ u))*angularY v θ u/(2*(Real.pi:ℂ)) := by
  rw [chart_root_eq_physical]
  exact micro_regular_onebody_pullback s v θ u hg hd hn

 theorem angularY_norm_real (v θ u : ℝ) : ‖angularY v θ (u:ℂ)‖=Real.exp v := by
  rw [angularY,Complex.norm_exp]
  simp

/-- The actual complete source pair agrees with its regular double-zero
extension, even at a collision of the two phases. No collision factor is
canceled from either side. -/
 theorem micro_regular_pair_source (s : ℂ) (v θ u₁ u₂ : ℝ) (hv : v < 0)
    (hg₁ : 0 < (angularG v θ (u₁:ℂ)).re)
    (hg₂ : 0 < (angularG v θ (u₂:ℂ)).re)
    (hi₁ : 0 < (chartW s v θ (u₁:ℂ)).im)
    (hi₂ : 0 < (chartW s v θ (u₂:ℂ)).im) :
    branchCompletePair (s,chartPhase s v θ (u₁:ℂ),chartPhase s v θ (u₂:ℂ)) =
      canceledPair (angularY v θ (u₁:ℂ)) (angularY v θ (u₂:ℂ))
        (globalRoot s (angularY v θ (u₁:ℂ))) (globalRoot s (angularY v θ (u₂:ℂ))) := by
  let p := chartPhase s v θ (u₁:ℂ)
  let q := chartPhase s v θ (u₂:ℂ)
  have hy₁ : ‖angularY v θ (u₁:ℂ)‖ < 1 := by rw [angularY_norm_real,Real.exp_lt_one_iff]; exact hv
  have hy₂ : ‖angularY v θ (u₂:ℂ)‖ < 1 := by rw [angularY_norm_real,Real.exp_lt_one_iff]; exact hv
  have hz₁ : ‖Complex.exp (-Complex.I*p)‖ < 1 := by
    rw [← chart_root_eq_physical s v θ (u₁:ℂ)]
    exact interiorRoot_norm_lt_one hi₁
  have hz₂ : ‖Complex.exp (-Complex.I*q)‖ < 1 := by
    rw [← chart_root_eq_physical s v θ (u₂:ℂ)]
    exact interiorRoot_norm_lt_one hi₂
  have hyden := one_sub_mul_ne_zero_of_norm_lt_one hy₁ hy₂
  have hzden := one_sub_mul_ne_zero_of_norm_lt_one hz₁ hz₂
  have hreg₁ : regularY s p=angularY v θ (u₁:ℂ) := regularY_chartPhase s v θ (u₁:ℂ) hg₁
  have hreg₂ : regularY s q=angularY v θ (u₂:ℂ) := regularY_chartPhase s v θ (u₂:ℂ) hg₂
  have hd : 1-(regularY s p*regularY s q)⁻¹ ≠ 0 := by
    rw [hreg₁,hreg₂]
    intro he
    have hx := inv_eq_one.mp (sub_eq_zero.mp he).symm
    exact hyden (by rw [hx]; simp)
  have he : 1-Complex.exp (-Complex.I*p)*Complex.exp (-Complex.I*q) =
      (p+q)*exponentialQuotient (p+q) := by
    rw [mul_exponentialQuotient,← Complex.exp_add]
    congr 2
    ring
  have hsum : p+q ≠ 0 := by
    intro hh
    apply hzden
    rw [he,hh,zero_mul]
  have hJ : exponentialQuotient (p+q) ≠ 0 := by
    intro hh
    apply hzden
    rw [he,hh,mul_zero]
  have hh := branchCompletePair_eq_rational s p q hd hsum hJ
  rw [hreg₁,hreg₂] at hh
  rw [chart_root_eq_physical s v θ (u₁:ℂ),chart_root_eq_physical s v θ (u₂:ℂ)]
  exact hh

 theorem micro_original_onebody_source (s : ℂ) (v θ u : ℝ) (hv : v < 0)
    (hg : 0 < (angularG v θ (u:ℂ)).re)
    (hi : 0 < (chartW s v θ (u:ℂ)).im) :
    chartB s v θ (u:ℂ)*microRegularOneBody s (chartPhase s v θ (u:ℂ)) =
      residueFactor (globalRoot s (angularY v θ (u:ℂ)))*angularY v θ (u:ℂ)/(2*(Real.pi:ℂ)) := by
  have hy : ‖angularY v θ (u:ℂ)‖ < 1 := by rw [angularY_norm_real,Real.exp_lt_one_iff]; exact hv
  have hz : ‖Complex.exp (-Complex.I*chartPhase s v θ (u:ℂ))‖ < 1 := by
    rw [← chart_root_eq_physical]
    exact interiorRoot_norm_lt_one hi
  have hyden := one_sub_mul_ne_zero_of_norm_lt_one hy hy
  have hzden := one_sub_mul_ne_zero_of_norm_lt_one hz hz
  have hd : 1-(angularY v θ (u:ℂ))^(-2:ℤ) ≠ 0 := by
    simp only [zpow_neg,zpow_ofNat]
    intro he
    have hx := inv_eq_one.mp (sub_eq_zero.mp he).symm
    apply hyden
    rw [← pow_two,hx]
    simp
  have hn : Complex.sin (chartPhase s v θ (u:ℂ)) ≠ 0 := by
    intro he
    apply hzden
    rw [← pow_two,complex_phase_one_sub_sq,he]
    ring
  exact micro_regular_onebody_source s v θ (u:ℂ) hg hd hn

end
end IsingBulk.Tail
