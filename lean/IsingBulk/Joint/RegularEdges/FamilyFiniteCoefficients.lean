import IsingBulk.Joint.RegularEdges.FamilyFiniteHigher

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Actual analyticity and positivity persist on one common family disk. -/
theorem compact_family_upper_data (B S : ℂ × E → ℂ)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      AnalyticAt ℂ B (u,eta) ∧ AnalyticAt ℂ S (u,eta) ∧ 0<(B (u,eta)).im ∧ S (u,eta)≠0 := by
  let U := {p : ℂ × E | AnalyticAt ℂ B p ∧ AnalyticAt ℂ S p ∧ 0<(B p).im ∧ S p≠0}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact hp.1.eventually_analyticAt.and (hp.2.1.eventually_analyticAt.and
      (((Complex.continuous_im.continuousAt.comp hp.1.continuousAt).eventually_const_lt hp.2.2.1).and
        (hp.2.1.continuousAt.eventually_ne hp.2.2.2)))
  exact Negative.compact_product_tube hQ hU
    (fun eta heta => ⟨hB eta heta,hS eta heta,hBi eta heta,hS0 eta heta⟩)

/-- Genuine coefficient differentiation under the complete integral holds on
one common upper-side disk for every particle and derivative order. -/
theorem compact_family_coefficient_jet_identity (B S : ℂ × E → ℂ) (b : ℝ)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀n j : ℕ,
      iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta))) u=
        edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n:=n) b
          (fun u=>B (u,eta)) (fun u=>S (u,eta)) j u := by
  obtain ⟨δ,hδ,hdata⟩ := compact_family_upper_data B S hQ hB hBi hS hS0
  refine ⟨δ,hδ,?_⟩
  intro eta heta u hu hi n j
  let U : Set ℂ := {u | ‖u‖<δ ∧ 0<u.im}
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  apply angularCoefficient_iteratedDeriv hU (B:=fun u=>B (u,eta)) (S:=fun u=>S (u,eta))
    (fun v hv=>(hdata eta heta v hv.1).1.comp (f:=fun u : ℂ => (u,eta))
      (analyticAt_id.prod analyticAt_const))
    (fun v hv=>(hdata eta heta v hv.1).2.1.comp (f:=fun u : ℂ => (u,eta))
      (analyticAt_id.prod analyticAt_const))
    (fun _ hv=>hv.2)
    (fun v hv=>(hdata eta heta v hv.1).2.2.1)
    (fun v hv=>(hdata eta heta v hv.1).2.2.2) n j ⟨hu,hi⟩

/-- Common lower nonresonant bounds for literal full coefficient derivatives. -/
theorem compact_family_nonresonant_coefficient_bound {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)≠1) (j : ℕ) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im →
      ‖iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta))) u‖≤C := by
  obtain ⟨a,C,ha,hC,hbound⟩ := compact_family_nonresonant_integral_bound B S hb hQ hB hBi hS hS0 hres j
  obtain ⟨r,hr,hid⟩ := compact_family_coefficient_jet_identity B S b hQ hB hBi hS hS0
  refine ⟨min a r,‖edgeCoefficientNormalization n‖*C,lt_min ha hr,by positivity,?_⟩
  intro eta heta u hu hi
  rw [hid eta heta u (hu.trans_le (min_le_right _ _)) hi n j,norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound eta heta u (hu.trans_le (min_le_left _ _))) (norm_nonneg _)

/-- Common higher finite bounds for literal full coefficient derivatives. -/
theorem compact_family_higher_coefficient_bound {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
        (Complex.I*(t:ℂ)^2)‖≤C := by
  obtain ⟨a,C,ha,hC,hbound⟩ := compact_family_higher_integral_bound hn hdegree B S hb hQ hB hBi hS hS0
  obtain ⟨r,hr,hid⟩ := compact_family_coefficient_jet_identity B S b hQ hB hBi hS hS0
  refine ⟨min a (Real.sqrt r),‖edgeCoefficientNormalization n‖*C,
    lt_min ha (Real.sqrt_pos.mpr hr),by positivity,?_⟩
  intro eta heta t ht htδ
  have htsq : t^2<r := by
    have hlt := htδ.trans_le (min_le_right _ _)
    nlinarith [Real.sq_sqrt hr.le]
  have hu : ‖Complex.I*(t:ℂ)^2‖<r := by simpa using htsq
  have hi : 0<(Complex.I*(t:ℂ)^2).im := by
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    positivity
  rw [hid eta heta _ hu hi n j,norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound eta heta t ht (htδ.trans_le (min_le_left _ _))) (norm_nonneg _)

end
end IsingBulk.Joint.RegularEdges
