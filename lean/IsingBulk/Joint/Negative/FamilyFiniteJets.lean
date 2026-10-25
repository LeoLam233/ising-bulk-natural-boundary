import IsingBulk.Joint.Negative.FixedParticle
import IsingBulk.Joint.Negative.CompactFamilies
import IsingBulk.Joint.FormFactors.CompactIntegralJets

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators

/-- Actual joint complex smoothness of every fixed odd negative-edge coefficient.
All derivatives are derived from its genuine compact angular integral. -/
theorem continuedAngularCoefficient_negative_contDiffAt (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} {K : Coupling} (hS : S K≠0)
    (hedge : A K+T K=(b:ℂ)*S K) (hb : |b|<1) (hB : 0<(-T K/S K).im) :
    ContDiffAt ℂ j (continuedAngularCoefficient n) K := by
  let ψ : (Fin n→ℝ)→(Fin (n+1)→ℂ) :=
    fun q i => (physicalDependentAngles n q i:ℂ)
  have hψ : Continuous ψ := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  let F : Coupling × (Fin (n+1)→ℂ)→ℂ := fun p => continuedAngularDensity p.1 p.2
  have hF0 (q : Fin n→ℝ) : AnalyticAt ℂ F (K,ψ q) :=
    continuedAngularDensity_negative_joint_analyticAt hn hS hedge hb hB
      (physicalDependentAngles n q) (physicalDependentAngles_sum_zero n q)
  have hev : ∀ᶠ L in 𝓝 K,∀q∈angleBox n,AnalyticAt ℂ F (L,ψ q) := by
    apply (isCompact_Icc : IsCompact (angleBox n)).eventually_forall_of_forall_eventually
    intro q _
    have hc : Continuous (fun p : Coupling × (Fin n→ℝ) => (p.1,ψ p.2)) :=
      continuous_fst.prodMk (hψ.comp continuous_snd)
    exact hc.continuousAt.eventually (hF0 q).eventually_analyticAt
  obtain ⟨U,hU,hUo,hKU⟩ := _root_.mem_nhds_iff.mp hev
  have hc := FormFactors.compact_analytic_integral_contDiffAt j (μ:=volume)
    (show IsCompact (angleBox n) from isCompact_Icc) hUo F ψ hψ hU hKU
  exact (contDiffAt_const (c:=((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n)).mul hc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- No finite-dimensionality assumption on the complex family parameter is
needed: the actual independent-coupling integral is composed with the family. -/
theorem weighted_coefficient_negative_joint_contDiffAt (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {eta : E}
    (hc : AnalyticAt ℂ curve (0,eta)) (ha : AnalyticAt ℂ amp (0,eta))
    (hS : S (curve (0,eta))≠0)
    (hedge : A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hb : |b|<1) (hB : 0<(-T (curve (0,eta))/S (curve (0,eta))).im) :
    ContDiffAt ℂ j (fun q => amp q^(n+1)*continuedAngularCoefficient n (curve q)) (0,eta) := by
  exact (ha.contDiffAt.pow _).mul
    ((continuedAngularCoefficient_negative_contDiffAt n j hn hS hedge hb hB).comp _ hc.contDiffAt)

/-- Taking the actual first-coordinate derivative loses exactly one order of
joint smoothness; equality with the Frechet derivative is proved on a neighborhood. -/
theorem parameterDeriv_contDiffAt {f : ℂ × E→ℂ} {p : ℂ × E} (j : ℕ)
    (hf : ContDiffAt ℂ (j+1) f p) : ContDiffAt ℂ j (parameterDeriv f) p := by
  let L : ((ℂ × E)→L[ℂ]ℂ)→L[ℂ]ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hg : ContDiffAt ℂ j (fun q => fderiv ℂ f q (1,0)) p :=
    L.contDiff.contDiffAt.comp p (hf.fderiv_right (by simp))
  apply hg.congr_of_eventuallyEq
  filter_upwards [hf.eventually (by simp)] with q hq
  have hsection : HasDerivAt (fun s : ℂ => (s,q.2)) (1,0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hq.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q.1 hsection |>.deriv

theorem jointParameterJet_contDiffAt {f : ℂ × E→ℂ} {p : ℂ × E} (j k : ℕ)
    (hf : ContDiffAt ℂ (j+k) f p) : ContDiffAt ℂ j (jointParameterJet f k) p := by
  induction k generalizing j with
  | zero => simpa only [Nat.cast_zero,add_zero,jointParameterJet,Function.iterate_zero,Function.id_def] using hf
  | succ k ih =>
    have h := parameterDeriv_contDiffAt j (ih (j+1) (by convert hf using 1; norm_cast; omega))
    simpa only [jointParameterJet,Function.iterate_succ',Function.comp_apply] using h

omit [NormedSpace ℂ E] in
/-- Compactness upgrades genuine joint continuity to a single complex disk,
without choosing a separate radius for each member. -/
theorem compact_joint_continuous_zero_difference (f : ℂ × E→ℂ) {Q : Set E}
    (hQ : IsCompact Q) (hf : ∀eta∈Q,ContinuousAt f (0,eta)) {ε : ℝ} (hε : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℂ,‖t‖<δ → ‖f (t,eta)-f (0,eta)‖<ε := by
  have hev : ∀ᶠ t in 𝓝 (0:ℂ),∀eta∈Q,‖f (t,eta)-f (0,eta)‖<ε := by
    apply hQ.eventually_forall_of_forall_eventually
    intro eta heta
    have hc : ContinuousAt (fun p : ℂ × E => f p-f (0,p.2)) (0,eta) :=
      (hf eta heta).sub ((hf eta heta).comp (f:=fun p : ℂ × E => (0,p.2))
        (continuous_const.prodMk continuous_snd).continuousAt)
    exact hc.norm.eventually_lt_const (by simpa using hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨δ,hδ,fun eta heta t ht => hball (by simpa using ht) eta heta⟩

/-- Uniform approach of every literal fixed negative coefficient derivative. -/
theorem compact_family_weighted_negative_jet_limit (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {Q : Set E} (hQ : IsCompact Q)
    (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta)) (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hedge : ∀eta∈Q,A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hb : |b|<1) (hB : ∀eta∈Q,0<(-T (curve (0,eta))/S (curve (0,eta))).im) :
    TendstoUniformlyOn (fun ε : ℝ => fun eta => iteratedDeriv j
      (fun t => amp (t,eta)^(n+1)*continuedAngularCoefficient n (curve (t,eta))) (-(ε:ℂ)))
      (fun eta => iteratedDeriv j
      (fun t => amp (t,eta)^(n+1)*continuedAngularCoefficient n (curve (t,eta))) 0) (𝓝[>] 0) Q := by
  let f : ℂ × E→ℂ := fun q => amp q^(n+1)*continuedAngularCoefficient n (curve q)
  have hcont : ∀eta∈Q,ContinuousAt (jointParameterJet f j) (0,eta) := by
    intro eta heta
    have hh := weighted_coefficient_negative_joint_contDiffAt n j hn (hc eta heta) (ha eta heta)
      (hS eta heta) (hedge eta heta) hb (hB eta heta)
    exact (jointParameterJet_contDiffAt 0 j (f:=f) (by simpa only [Nat.cast_zero,zero_add] using hh)).continuousAt
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := compact_joint_continuous_zero_difference (jointParameterJet f j) hQ hcont hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht eta heta
  have hh := hbound eta heta (-(t:ℂ)) (by simpa [abs_of_pos ht.1] using ht.2)
  simpa only [dist_eq_norm,norm_sub_rev,jointParameterJet_eq,←iteratedDeriv_eq_iterate,f] using hh

end
end IsingBulk.Joint.Negative
