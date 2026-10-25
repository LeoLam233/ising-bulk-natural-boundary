import IsingBulk.Joint.RegularEdges.FamilyParityLeading

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Family
variable {b : ℝ} (B S : ℂ × E→ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
  (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
  (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
include hb hQ hB hBi hS hS0

/-- The entire odd family has a common nonzero first singular coefficient,
all lower scaled derivatives vanish uniformly, and the full derivative grows
past every bound simultaneously on the compact family. -/
theorem odd_compact_family_parity_first_singularity {q k : ℕ} (hq : 1≤q)
    (hcritical : 2*k+1=(2*q+1)^2) (hres : continuedRoot (b:ℂ)^(2*q+1)=1)
    (hearly : ∀i<q,continuedRoot (b:ℂ)^(2*i+1)≠1) :
    ∃c : ℝ,0<c ∧
      (∀eta∈Q,c≤‖edgeCoefficientLeading (2*q) k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^2) • iteratedDeriv j
        (paritySeries 0 b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then edgeCoefficientLeading (2*q) k b (fun u=>B (u,eta)) (fun u=>S (u,eta)) else 0)
        (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (paritySeries 0 b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨hk,hdegree⟩ := odd_first_degree hq hcritical
  have hb' := abs_lt.mp hb
  have hQpos : 0<(2*q+1:ℝ)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  have hp := odd_shapePeriod_continuousOn (by omega : 1≤2*q) hdegree hQpos
  have hp' : ContinuousOn (shapePeriod (2*q) k ((2*q+1)/Real.sqrt (1-b^2))) {c : ℂ | 0<c.re} := by
    simpa only [Nat.sub_add_cancel hk] using hp
  have hall (j : ℕ) (hj : j≤k) := compact_family_parity_derivative_uniform_limit B S hb hQ hB hBi hS hS0
    (e:=0) (p:=q) (k:=k) (a:=2) (by omega) (by nlinarith : q<k+2)
    (by simpa using hres) (by simpa using hearly)
    (fun i hi=>by simpa using odd_higher_degree hcritical hi)
    (by simpa using odd_first_balance hcritical) (by simpa using odd_first_majorant_integrable hq hcritical)
    (by simpa using hp') j hj
  have hBc : ContinuousOn (fun eta=>B (0,eta)) Q := fun eta heta=>
    ((hB eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hSc : ContinuousOn (fun eta=>S (0,eta)) Q := fun eta heta=>
    ((hS eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨c,hc,hbound⟩ := odd_family_leading_amplitude_lower_bound (B := fun eta u=>B (u,eta)) (S := fun eta u=>S (u,eta)) hQ hBc hSc hBi hS0
    (by omega : 1≤2*q) hdegree hb hres
  have hbound' : ∀eta∈Q,c≤‖edgeCoefficientLeading (2*q) k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖ := by
    simpa only [Nat.sub_add_cancel hk] using hbound
  refine ⟨c,hc,hbound',by simpa only [Nat.add_zero] using hall,?_⟩
  apply uniform_scaled_leading_unbounded hc hbound' (a:=2) (by omega)
  simpa only [Nat.add_zero,ite_true,Complex.real_smul] using hall k le_rfl

/-- Complete nonzero-even family counterpart; no omitted finite prefix. -/
theorem even_compact_family_parity_first_singularity {q k : ℕ}
    (hcritical : 2*(k+1)=(2*q+2)^2) (hres : continuedRoot (b:ℂ)^(2*q+2)=1)
    (hearly : ∀i<q,continuedRoot (b:ℂ)^(2*i+2)≠1) :
    ∃c : ℝ,0<c ∧
      (∀eta∈Q,c≤‖edgeCoefficientLeading (2*q+1) k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>t • iteratedDeriv j
        (paritySeries 1 b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then edgeCoefficientLeading (2*q+1) k b (fun u=>B (u,eta)) (fun u=>S (u,eta)) else 0)
        (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (paritySeries 1 b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  have hb' := abs_lt.mp hb
  have hQpos : 0<(2*q+1+1:ℝ)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  have hp := even_shapePeriod_continuousOn (by omega : 1≤2*q+1) (even_first_degree hcritical) hQpos
  have hall (j : ℕ) (hj : j≤k) := compact_family_parity_derivative_uniform_limit B S hb hQ hB hBi hS hS0
    (e:=1) (p:=q) (k:=k) (a:=1) (by omega) (by nlinarith : q<k+2)
    (by simpa only [Nat.add_assoc] using hres) (by simpa only [Nat.add_assoc] using hearly)
    (fun i hi=>even_higher_degree hcritical hi)
    (even_first_balance hcritical) (even_first_majorant_integrable hcritical)
    (by simpa using hp) j hj
  have hBc : ContinuousOn (fun eta=>B (0,eta)) Q := fun eta heta=>
    ((hB eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hSc : ContinuousOn (fun eta=>S (0,eta)) Q := fun eta heta=>
    ((hS eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨c,hc,hbound⟩ := even_family_leading_amplitude_lower_bound (B := fun eta u=>B (u,eta)) (S := fun eta u=>S (u,eta)) hQ hBc hSc hBi hS0
    (by omega : 1≤2*q+1) (even_first_degree hcritical) hb (by simpa only [Nat.add_assoc] using hres)
  refine ⟨c,hc,hbound,by simpa only [pow_one] using hall,?_⟩
  apply uniform_scaled_leading_unbounded hc hbound (a:=1) (by omega)
  simpa only [ite_true,Complex.real_smul] using hall k le_rfl

end Family
end
end IsingBulk.Joint.RegularEdges
