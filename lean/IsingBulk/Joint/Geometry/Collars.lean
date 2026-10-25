import IsingBulk.Joint.Geometry.Components
import IsingBulk.Joint.Final.LocalExtension
import Mathlib.Analysis.Convex.Topology

namespace IsingBulk.Joint
noncomputable section
open Set Metric
open scoped Topology

/-- An inward motion into an interior ball yields the literal component collar. -/
theorem hasLocalCollar_of_inward_motion {D : Set Coupling} (hD : IsOpen D)
    (hm : ∀ P ∈ frontier D, ∀ ε > (0 : ℝ), ∃ f : Coupling → Coupling,
      Continuous f ∧ f P ∈ D ∩ ball P ε ∧
      ∀ Q ∈ D, segment ℝ Q (f Q) ⊆ D) : HasLocalCollar D := by
  intro P hP U hU hPU a ha hPa
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU P hPU
  obtain ⟨f,hf,hfP,hseg⟩ := hm P hP ε hε
  obtain ⟨δ,hδ,hδD⟩ := Metric.isOpen_iff.mp (hD.inter isOpen_ball) (f P) hfP
  let V := ball P ε ∩ f ⁻¹' ball (f P) δ
  have hV : IsOpen V := isOpen_ball.inter (isOpen_ball.preimage hf)
  have hPV : P ∈ V := ⟨mem_ball_self hε,mem_ball_self hδ⟩
  have hVU : V ⊆ U := fun _ h => hεU h.1
  have hcommon : D ∩ V ⊆ connectedComponentIn (D ∩ U) (f P) := by
    intro Q hQ
    have hball : ball (f P) δ ⊆ connectedComponentIn (D ∩ U) (f P) := by
      apply (convex_ball (f P) δ).isPreconnected.subset_connectedComponentIn (mem_ball_self hδ)
      intro x hx
      exact ⟨(hδD hx).1,hεU (hδD hx).2⟩
    have hfQ : f Q ∈ connectedComponentIn (D ∩ U) (f P) := hball hQ.2.2
    have hsq : segment ℝ Q (f Q) ⊆ D ∩ U := by
      intro x hx
      exact ⟨hseg Q hQ.1 hx,hεU ((convex_ball P ε).segment_subset hQ.2.1
        (hδD hQ.2.2).2 hx)⟩
    have hsame := (convex_segment (𝕜 := ℝ) Q (f Q)).isPreconnected.subset_connectedComponentIn
      (right_mem_segment ℝ Q (f Q)) hsq (left_mem_segment ℝ Q (f Q))
    rw [connectedComponentIn_eq hfQ]
    exact hsame
  obtain ⟨b,hbV,hba⟩ := mem_closure_iff.mp hPa V hV hPV
  have hbD := (connectedComponentIn_subset (D ∩ U) a hba).1
  have hbf := hcommon ⟨hbD,hbV⟩
  refine ⟨V,hV,hPV,hVU,?_⟩
  rw [connectedComponentIn_eq hba,← connectedComponentIn_eq hbf]
  exact hcommon


private theorem closure_inequality {f g : Coupling → ℝ} (hf : Continuous f) (hg : Continuous g)
    {D : Set Coupling} (h : ∀ K ∈ D, f K < g K) :
    ∀ K ∈ closure D, f K ≤ g K :=
  closure_minimal (fun K hK => (h K hK).le) (isClosed_le hf hg)

theorem closure_high_inequalities {K : Coupling} (hK : K ∈ closure highDomain) :
    Real.cosh K.1.re * Real.tanh |K.2.re| ≤ Real.cos K.1.im ∧
    Real.cosh K.2.re * Real.tanh |K.1.re| ≤ Real.cos K.2.im := by
  exact ⟨closure_inequality (by fun_prop) (by fun_prop) (fun _ h => h.2.2.1) K hK,
    closure_inequality (by fun_prop) (by fun_prop) (fun _ h => h.2.2.2) K hK⟩

theorem closure_low_inequalities {K : Coupling} (hK : K ∈ closure lowDomain) :
    |Real.cos K.1.im| ≤ Real.cosh K.1.re * Real.tanh K.2.re ∧
    |Real.cos K.2.im| ≤ Real.cosh K.2.re * Real.tanh K.1.re := by
  exact ⟨closure_inequality (by fun_prop) (by fun_prop) (fun _ h => h.2.2.1) K hK,
    closure_inequality (by fun_prop) (by fun_prop) (fun _ h => h.2.2.2) K hK⟩

private theorem high_scaled_strict {x u y t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hy : |y| ≤ Real.pi / 2) (hg : Real.cosh x * Real.tanh |u| ≤ Real.cos y) :
    Real.cosh (t*x) * Real.tanh |t*u| < Real.cos (t*y) := by
  have hy' : |t*y| < Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg ht]
    calc t * |y| ≤ t * (Real.pi / 2) := mul_le_mul_of_nonneg_left hy ht
         _ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  by_cases hu : u = 0
  · simp only [hu,mul_zero,abs_zero,Real.tanh_zero,mul_zero]
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hy')
  have hc : Real.cosh (t*x) ≤ Real.cosh x := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_le_of_le_one_left (abs_nonneg x) ht1.le
  have htanh : Real.tanh |t*u| < Real.tanh |u| := by
    apply IsingBulk.Anisotropic.tanh_strictMono
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_lt_of_lt_one_left (abs_pos.mpr hu) ht1
  have hn : 0 ≤ Real.tanh |t*u| := by
    simpa using IsingBulk.Anisotropic.tanh_strictMono.monotone (abs_nonneg (t*u))
  calc Real.cosh (t*x) * Real.tanh |t*u|
      ≤ Real.cosh x * Real.tanh |t*u| := mul_le_mul_of_nonneg_right hc hn
    _ < Real.cosh x * Real.tanh |u| := mul_lt_mul_of_pos_left htanh (Real.cosh_pos x)
    _ ≤ Real.cos y := hg
    _ ≤ Real.cos (t*y) := IsingBulk.Anisotropic.cos_scale_ge
      (by linarith [Real.pi_pos]) ht ht1.le

theorem scale_mem_high_of_nonstrict {K : Coupling}
    (hy : |K.1.im| ≤ Real.pi/2) (hv : |K.2.im| ≤ Real.pi/2)
    (hg₁ : Real.cosh K.1.re * Real.tanh |K.2.re| ≤ Real.cos K.1.im)
    (hg₂ : Real.cosh K.2.re * Real.tanh |K.1.re| ≤ Real.cos K.2.im)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : t • K ∈ highDomain := by
  have hscale : ∀ y : ℝ, |y| ≤ Real.pi/2 → |t*y| < Real.pi/2 := by
    intro y hy
    rw [abs_mul,abs_of_nonneg ht]
    calc t*|y| ≤ t*(Real.pi/2) := mul_le_mul_of_nonneg_left hy ht
         _ < Real.pi/2 := by nlinarith [Real.pi_pos]
  simpa only [highDomain,Set.mem_ofPred_eq,Prod.smul_fst,Prod.smul_snd,
    Complex.smul_re,Complex.smul_im,smul_eq_mul] using
    And.intro (hscale _ hy) (And.intro (hscale _ hv)
      (And.intro (high_scaled_strict ht ht1 hy hg₁) (high_scaled_strict ht ht1 hv hg₂)))

theorem scale_closure_high_mem {K : Coupling} (hK : K ∈ closure highDomain)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : t • K ∈ highDomain :=
  scale_mem_high_of_nonstrict (closure_high_bounds hK).1 (closure_high_bounds hK).2.1
    (closure_high_inequalities hK).1 (closure_high_inequalities hK).2 ht ht1

private theorem high_scale_segment {Q : Coupling} (hQ : Q ∈ highDomain)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : segment ℝ Q (t • Q) ⊆ highDomain := by
  have htQ : t • Q ∈ segment ℝ (0 : Coupling) Q := by
    refine ⟨1-t,t,by linarith,ht,by ring,?_⟩
    simp
  exact ((convex_segment (𝕜 := ℝ) 0 Q).segment_subset (right_mem_segment ℝ 0 Q) htQ).trans
    (highDomain_starConvex.segment_subset hQ)

theorem highDomain_hasLocalCollar : HasLocalCollar highDomain := by
  apply hasLocalCollar_of_inward_motion highDomain_isOpen
  intro P hP ε hε
  have hPc : P ∈ closure highDomain := frontier_subset_closure hP
  have hc : Continuous (fun t : ℝ => t • P) := by fun_prop
  have hN : (fun t : ℝ => t • P) ⁻¹' ball P ε ∈ 𝓝 (1 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_ball.mem_nhds (mem_ball_self (x := P) hε)
  have hcl : (1 : ℝ) ∈ closure (Ioo 0 1) := by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; simp
  obtain ⟨t,htN,ht⟩ := mem_closure_iff_nhds.mp hcl _ hN
  refine ⟨fun Q => t • Q,by fun_prop,⟨scale_closure_high_mem hPc ht.1.le ht.2,htN⟩,?_⟩
  intro Q hQ
  exact high_scale_segment hQ ht.1.le ht.2.le


private theorem low_raise_strict {x u δ : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hδ : 0 < δ) :
    Real.cosh x * Real.tanh u < Real.cosh (x+δ) * Real.tanh (u+δ) := by
  have hc : Real.cosh x ≤ Real.cosh (x+δ) := by
    rw [Real.cosh_le_cosh,abs_of_nonneg hx,abs_of_pos (by linarith)]
    linarith
  have hn : 0 ≤ Real.tanh u := by
    simpa using IsingBulk.Anisotropic.tanh_strictMono.monotone hu
  calc Real.cosh x * Real.tanh u ≤ Real.cosh (x+δ) * Real.tanh u :=
      mul_le_mul_of_nonneg_right hc hn
    _ < Real.cosh (x+δ) * Real.tanh (u+δ) :=
      mul_lt_mul_of_pos_left (IsingBulk.Anisotropic.tanh_strictMono (by linarith))
        (Real.cosh_pos _)

/-- A common positive real translation opens every low-temperature boundary point. -/
theorem raise_mem_low_of_nonstrict {K : Coupling}
    (hx : 0 ≤ K.1.re) (hu : 0 ≤ K.2.re)
    (hg₁ : |Real.cos K.1.im| ≤ Real.cosh K.1.re * Real.tanh K.2.re)
    (hg₂ : |Real.cos K.2.im| ≤ Real.cosh K.2.re * Real.tanh K.1.re)
    {δ : ℝ} (hδ : 0 < δ) : K + ((δ : ℂ),(δ : ℂ)) ∈ lowDomain := by
  refine ⟨by simpa using (show 0 < K.1.re+δ by linarith),
    by simpa using (show 0 < K.2.re+δ by linarith),?_,?_⟩
  · simpa using hg₁.trans_lt (low_raise_strict hx hu hδ)
  · simpa using hg₂.trans_lt (low_raise_strict hu hx hδ)


theorem raise_closure_low_mem {K : Coupling} (hK : K ∈ closure lowDomain)
    {δ : ℝ} (hδ : 0 < δ) : K + ((δ : ℂ),(δ : ℂ)) ∈ lowDomain :=
  raise_mem_low_of_nonstrict (closure_low_bounds hK).1 (closure_low_bounds hK).2.1
    (closure_low_inequalities hK).1 (closure_low_inequalities hK).2 hδ

private theorem low_raise_segment {Q : Coupling} (hQ : Q ∈ lowDomain)
    {δ : ℝ} (hδ : 0 ≤ δ) : segment ℝ Q (Q + ((δ : ℂ),(δ : ℂ))) ⊆ lowDomain := by
  rintro L ⟨a,b,ha,hb,hab,rfl⟩
  apply lowDomain_mono_re hQ
  · simp only [Prod.fst_add,Prod.smul_fst,Complex.add_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re]
    nlinarith [mul_nonneg hb hδ,congrArg (fun t : ℝ => t*Q.1.re) hab]
  · simp only [Prod.snd_add,Prod.smul_snd,Complex.add_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re]
    nlinarith [mul_nonneg hb hδ,congrArg (fun t : ℝ => t*Q.2.re) hab]
  · simp only [Prod.fst_add,Prod.smul_fst,Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.ofReal_im]
    nlinarith [congrArg (fun t : ℝ => t*Q.1.im) hab]
  · simp only [Prod.snd_add,Prod.smul_snd,Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.ofReal_im]
    nlinarith [congrArg (fun t : ℝ => t*Q.2.im) hab]

theorem lowDomain_hasLocalCollar : HasLocalCollar lowDomain := by
  apply hasLocalCollar_of_inward_motion lowDomain_isOpen
  intro P hP ε hε
  have hPc : P ∈ closure lowDomain := frontier_subset_closure hP
  have hc : Continuous (fun δ : ℝ => P + ((δ : ℂ),(δ : ℂ))) := by fun_prop
  have hN : (fun δ : ℝ => P + ((δ : ℂ),(δ : ℂ))) ⁻¹' ball P ε ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    change ball P ε ∈ 𝓝 (P + (0 : Coupling))
    simpa using isOpen_ball.mem_nhds (mem_ball_self (x := P) hε)
  have hcl : (0 : ℝ) ∈ closure (Ioi 0) := by rw [closure_Ioi]; simp
  obtain ⟨δ,hδN,hδ⟩ := mem_closure_iff_nhds.mp hcl _ hN
  refine ⟨fun Q => Q + ((δ : ℂ),(δ : ℂ)),by fun_prop,
    ⟨raise_closure_low_mem hPc hδ,hδN⟩,?_⟩
  intro Q hQ
  exact low_raise_segment hQ hδ.le


theorem closure_high_of_nonstrict {K : Coupling}
    (hy : |K.1.im| ≤ Real.pi/2) (hv : |K.2.im| ≤ Real.pi/2)
    (hg₁ : Real.cosh K.1.re * Real.tanh |K.2.re| ≤ Real.cos K.1.im)
    (hg₂ : Real.cosh K.2.re * Real.tanh |K.1.re| ≤ Real.cos K.2.im) :
    K ∈ closure highDomain := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have hc : Continuous (fun t : ℝ => t • K) := by fun_prop
  have hN : (fun t : ℝ => t • K) ⁻¹' U ∈ 𝓝 (1 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU
  have hcl : (1 : ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; simp
  obtain ⟨t,htN,ht⟩ := mem_closure_iff_nhds.mp hcl _ hN
  exact ⟨t • K,htN,scale_mem_high_of_nonstrict hy hv hg₁ hg₂ ht.1.le ht.2⟩


theorem closure_low_of_nonstrict {K : Coupling}
    (hx : 0 ≤ K.1.re) (hu : 0 ≤ K.2.re)
    (hg₁ : |Real.cos K.1.im| ≤ Real.cosh K.1.re * Real.tanh K.2.re)
    (hg₂ : |Real.cos K.2.im| ≤ Real.cosh K.2.re * Real.tanh K.1.re) :
    K ∈ closure lowDomain := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have hc : Continuous (fun δ : ℝ => K + ((δ : ℂ),(δ : ℂ))) := by fun_prop
  have hN : (fun δ : ℝ => K + ((δ : ℂ),(δ : ℂ))) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    change U ∈ 𝓝 (K + (0 : Coupling))
    simpa using hU
  have hcl : (0 : ℝ) ∈ closure (Ioi 0) := by rw [closure_Ioi]; simp
  obtain ⟨δ,hδN,hδ⟩ := mem_closure_iff_nhds.mp hcl _ hN
  exact ⟨K + ((δ : ℂ),(δ : ℂ)),hδN,raise_mem_low_of_nonstrict hx hu hg₁ hg₂ hδ⟩

end
end IsingBulk.Joint
