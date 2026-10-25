import IsingBulk.Joint.Geometry.Basic
import IsingBulk.Anisotropic.Geometry.HighTopology

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

theorem cosh_tanh_scale_le {x u b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.cosh (b*x) * Real.tanh |b*u| ≤ Real.cosh x * Real.tanh |u| := by
  have hc : Real.cosh (b*x) ≤ Real.cosh x := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (abs_nonneg x) hb1
  have ht : Real.tanh |b*u| ≤ Real.tanh |u| := by
    apply tanh_strictMono.monotone
    rw [abs_mul, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (abs_nonneg u) hb1
  have hn : 0 ≤ Real.tanh |b*u| := by
    simpa using tanh_strictMono.monotone (abs_nonneg (b*u))
  exact mul_le_mul hc ht hn (Real.cosh_pos _).le

theorem highDomain_starConvex : StarConvex ℝ (0 : Coupling) highDomain := by
  intro K hK a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  rcases hK with ⟨hy,hv,h₁,h₂⟩
  have hy' : |b*K.1.im| < Real.pi/2 := by
    rw [abs_mul, abs_of_nonneg hb]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) hb1) hy
  have hv' : |b*K.2.im| < Real.pi/2 := by
    rw [abs_mul, abs_of_nonneg hb]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) hb1) hv
  have h₁' := lt_of_le_of_lt (cosh_tanh_scale_le (x:=K.1.re) (u:=K.2.re) hb hb1) h₁
  have h₂' := lt_of_le_of_lt (cosh_tanh_scale_le (x:=K.2.re) (u:=K.1.re) hb hb1) h₂
  have hc₁ := cos_scale_ge (y:=K.1.im) (by linarith [Real.pi_pos]) hb hb1
  have hc₂ := cos_scale_ge (y:=K.2.im) (by linarith [Real.pi_pos]) hb hb1
  simpa only [smul_zero, zero_add, highDomain, Set.mem_ofPred_eq, Prod.smul_fst,
    Prod.smul_snd, Complex.smul_re, Complex.smul_im, smul_eq_mul] using
    And.intro hy' (And.intro hv' (And.intro (lt_of_lt_of_le h₁' hc₁) (lt_of_lt_of_le h₂' hc₂)))

theorem origin_mem_highDomain : (0 : Coupling) ∈ highDomain := by
  simp only [highDomain, Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero,
    Complex.zero_im, Complex.zero_re, abs_zero, Real.cosh_zero, Real.tanh_zero,
    Real.cos_zero, mul_zero]
  constructor
  · positivity
  constructor
  · positivity
  norm_num

theorem highDomain_contractible : ContractibleSpace highDomain :=
  highDomain_starConvex.contractibleSpace ⟨0,origin_mem_highDomain⟩

end
end IsingBulk.Joint
