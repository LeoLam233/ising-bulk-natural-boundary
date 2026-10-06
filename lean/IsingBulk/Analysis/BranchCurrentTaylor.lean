import IsingBulk.Analysis.BranchInclusion

/-! The current normal form at the actual radial center. Its real remainder
allows the source's quadratic displacement of the branch center. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem current_remainder_identity (d : LocalBranchData) (ε t u : ℝ) (hε : 1+ε ≠ 0) :
    currentD d ε t u-((d.a:ℂ)*u-Complex.I*((d.b:ℂ)*ε+(d.a:ℂ)*d.tau*t/2)) =
      (Complex.cosh (-(d.thetaB:ℂ)*Complex.I+
          (-(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2+(u:ℂ)*Complex.I))-
        (Real.cos d.thetaB:ℂ)+Complex.I*(d.a:ℂ)*
          (-(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2+(u:ℂ)*Complex.I))-
      ((ε^2/(1+ε):ℝ):ℂ)*((Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ)) := by
  have ha : (Real.cos d.thetaB:ℂ) = 2*(Real.cos d.theta:ℂ)-1 := by
    exact_mod_cast d.angle_relation
  rw [← branchDModel_eq d ε t u hε]
  unfold branchDModel radialTraceModel LocalBranchData.b LocalBranchData.a
  push_cast
  push_cast at ha
  rw [ha]
  have he : -(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2+(-(d.thetaB:ℂ)+(u:ℂ))*Complex.I =
      -(d.thetaB:ℂ)*Complex.I+(-(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2+(u:ℂ)*Complex.I) := by ring
  rw [he]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem current_normal_form (d : LocalBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 ≤ ε → ε < r → 0 ≤ t → t < r → |u| < r →
      ‖currentD d ε t u-((d.a:ℂ)*u-
        Complex.I*((d.b:ℂ)*ε+(d.a:ℂ)*d.tau*t/2))‖ ≤
        C*(u^2+(ε+d.tau*t)^2) := by
  obtain ⟨K,hK,hb⟩ := shifted_cosh_remainder d.thetaB
  obtain ⟨η,hη,hball⟩ := Metric.eventually_nhds_iff.mp hb
  let r := η/(2*(d.c₀+d.tau+1))
  let C := 2*K*((d.c₀+1)^2+1)+2
  have hc := d.c₀_pos
  have hτ := d.tau_pos
  refine ⟨C,r,by dsimp [C]; positivity,by dsimp [r]; positivity,?_⟩
  intro ε t u hε hεr ht htr hur
  let Q := ε+d.tau*t
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hεQ : ε ≤ Q := by dsimp [Q]; linarith [mul_nonneg hτ.le ht]
  let w : ℂ := -(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2+(u:ℂ)*Complex.I
  have hn : ‖w‖ ≤ d.c₀*ε+d.tau*t/2+|u| := by
    calc
      _ ≤ ‖-(d.c₀:ℂ)*ε+(d.tau:ℂ)*t/2‖+‖(u:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖-(d.c₀:ℂ)*ε‖+‖(d.tau:ℂ)*t/2‖+‖(u:ℂ)*Complex.I‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp [abs_of_pos hc,abs_of_pos hτ,abs_of_nonneg hε,abs_of_nonneg ht]
  have hwr : ‖w‖ < η := by
    have hsmall : d.c₀*ε+d.tau*t/2+|u| < (d.c₀+d.tau+1)*r := by
      nlinarith [mul_lt_mul_of_pos_left hεr hc,mul_lt_mul_of_pos_left htr hτ]
    have hrval : (d.c₀+d.tau+1)*r = η/2 := by dsimp [r]; field_simp
    linarith
  have hnQ : ‖w‖ ≤ (d.c₀+1)*Q+|u| := by
    apply hn.trans
    dsimp [Q]
    nlinarith [mul_nonneg hc.le (mul_nonneg hτ.le ht)]
  have hcos := hball (show dist w 0 < η by simpa using hwr)
  have hcoef : ‖(Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      show (1:ℝ)+1=2 by norm_num] using
        add_le_add (Real.abs_cos_le_one d.theta) (Real.abs_sin_le_one d.theta)
  have hfrac : 0 ≤ ε^2/(1+ε) := by positivity
  have hfrac' : ε^2/(1+ε) ≤ ε^2 := div_le_self (sq_nonneg _) (by linarith)
  rw [current_remainder_identity d ε t u (by linarith)]
  apply (norm_sub_le _ _).trans
  have hb₁ : ‖Complex.cosh (-(d.thetaB:ℂ)*Complex.I+w)-(Real.cos d.thetaB:ℂ)+
      Complex.I*(d.a:ℂ)*w‖ ≤ K*((d.c₀+1)*Q+|u|)^2 :=
    hcos.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnQ 2) hK.le)
  have hb₂ : ‖((ε^2/(1+ε):ℝ):ℂ)*((Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ))‖ ≤ 2*Q^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hfrac]
    nlinarith [mul_le_mul hfrac' hcoef (norm_nonneg _) (sq_nonneg ε),
      pow_le_pow_left₀ hε hεQ 2]
  have hpoly : ((d.c₀+1)*Q+|u|)^2 ≤ 2*((d.c₀+1)^2+1)*(u^2+Q^2) := by
    nlinarith [sq_nonneg ((d.c₀+1)*Q-|u|),sq_abs u,
      mul_nonneg (sq_nonneg (d.c₀+1)) (sq_nonneg u)]
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hpoly hK.le,sq_nonneg u]

/-- The actual imaginary part is kept exact; only the real component is a
quadratic remainder. In particular no sign is imposed at u=0. -/
theorem current_real_remainder (d : LocalBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 ≤ ε → ε < r → 0 ≤ t → t < r → |u| < r →
      |(currentD d ε t u).re-d.a*u| ≤ C*(u^2+(ε+d.tau*t)^2) := by
  obtain ⟨C,r,hC,hr,h⟩ := current_normal_form d
  refine ⟨C,r,hC,hr,?_⟩
  intro ε t u hε hεr ht htr hur
  have hb := (Complex.abs_re_le_norm (currentD d ε t u-((d.a:ℂ)*u-
    Complex.I*((d.b:ℂ)*ε+(d.a:ℂ)*d.tau*t/2)))).trans (h ε t u hε hεr ht htr hur)
  simpa [Complex.sub_re,Complex.mul_re,Complex.mul_im] using hb

end
end IsingBulk.Branch
