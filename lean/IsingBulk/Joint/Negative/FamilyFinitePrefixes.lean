import IsingBulk.Joint.Negative.FamilyFiniteJets

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- One compact-family disk works simultaneously for every member of a finite
collection of genuinely jointly continuous functions. -/
theorem compact_finite_joint_continuous_difference {I : Type*} (F : Finset I)
    (f : I→ℂ × E→ℂ) {Q : Set E} (hQ : IsCompact Q)
    (hf : ∀i∈F,∀eta∈Q,ContinuousAt (f i) (0,eta)) {ε : ℝ} (hε : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℂ,‖t‖<δ → ∀i∈F,‖f i (t,eta)-f i (0,eta)‖<ε := by
  have hev : ∀ᶠ t in 𝓝 (0:ℂ),∀i∈F,∀eta∈Q,‖f i (t,eta)-f i (0,eta)‖<ε := by
    rw [Finset.eventually_all]
    intro i hi
    obtain ⟨δ,hδ,hbound⟩ := compact_joint_continuous_zero_difference (f i) hQ (hf i hi) hε
    filter_upwards [ball_mem_nhds (0:ℂ) hδ] with t ht eta heta
    exact hbound eta heta t (by simpa using ht)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨δ,hδ,fun eta heta t ht i hi => hball (by simpa using ht) i hi eta heta⟩

/-- Genuine common finite-prefix uniform continuity for the literal weighted
odd coefficients and every transverse derivative through J. The approaching
point may be anywhere in the complex disk, not only on the inward real ray. -/
theorem compact_family_weighted_negative_finite_jets {b : ℝ}
    (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {Q : Set E} (hQ : IsCompact Q)
    (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta)) (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hedge : ∀eta∈Q,A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hb : |b|<1) (hB : ∀eta∈Q,0<(-T (curve (0,eta))/S (curve (0,eta))).im)
    (F : Finset ℕ) (hodd : ∀n∈F,Odd (n+1)) (J : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℂ,‖t‖<δ → ∀n∈F,∀j≤J,
      ‖iteratedDeriv j (fun u => amp (u,eta)^(n+1)*continuedAngularCoefficient n (curve (u,eta))) t-
        iteratedDeriv j (fun u => amp (u,eta)^(n+1)*continuedAngularCoefficient n (curve (u,eta))) 0‖<ε := by
  let f := fun (v : ℕ × ℕ) => jointParameterJet
    (fun q : ℂ × E => amp q^(v.1+1)*continuedAngularCoefficient v.1 (curve q)) v.2
  have hf : ∀v∈F ×ˢ Finset.range (J+1),∀eta∈Q,ContinuousAt (f v) (0,eta) := by
    intro v hv eta heta
    have hh := weighted_coefficient_negative_joint_contDiffAt v.1 v.2
      (hodd v.1 (Finset.mem_product.mp hv).1) (hc eta heta) (ha eta heta)
      (hS eta heta) (hedge eta heta) hb (hB eta heta)
    exact (jointParameterJet_contDiffAt 0 v.2 (by simpa only [Nat.cast_zero,zero_add] using hh)).continuousAt
  obtain ⟨δ,hδ,hbound⟩ := compact_finite_joint_continuous_difference
    (F ×ˢ Finset.range (J+1)) f hQ hf hε
  refine ⟨δ,hδ,?_⟩
  intro eta heta t ht n hn j hj
  have hh := hbound eta heta t ht (n,j) (Finset.mem_product.mpr ⟨hn,Finset.mem_range.mpr (by omega)⟩)
  simpa only [f,jointParameterJet_eq,←iteratedDeriv_eq_iterate] using hh

end
end IsingBulk.Joint.Negative
