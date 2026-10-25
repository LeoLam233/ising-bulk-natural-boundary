import IsingBulk.Joint.Negative.FamilyBoundaryIdentity

/-! # Uniform all-index jets of the actual odd coefficients
No physical-side map, inward path or auxiliary inverse coordinate is assumed.
The physical scale and varying anisotropy are constructed from the joint family.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Joint.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A single Cauchy estimate for every actual odd boundary coefficient and every
member of an arbitrary compact bounded holomorphic family. The constants precede
both derivative order and particle number, and include the entire finite prefix. -/
theorem compact_actual_odd_boundary_cauchy
    {b : ℝ} {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hb : |b|<1) (hQ : IsCompact Q)
    (hc : ∀ eta∈Q, AnalyticAt ℂ curve (0,eta))
    (ha : ∀ eta∈Q, AnalyticAt ℂ amp (0,eta))
    (hS : ∀ eta∈Q, S (curve (0,eta))≠0)
    (hamp : ∀ eta∈Q, amp (0,eta)≠0)
    (he : ∀ eta∈Q, A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)))
    (hB : ∀ eta∈Q, 0<(-T (curve (0,eta))/S (curve (0,eta))).im) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ eta∈Q, ∀ (j n : ℕ), Odd (n+1) →
        ‖iteratedDeriv j
          (fun t => amp (t,eta)^(n+1)*continuedAngularCoefficient n (curve (t,eta))) 0‖≤
          (j.factorial:ℝ)*(K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/((n+1:ℕ):ℝ)^3)^j := by
  let H : ℂ × E→NumeratorParameter := fun q => physicalNegativeParameter b (curve q) (amp q)
  obtain ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,hbound⟩ :=
    compact_family_odd_integrand_cauchy H hb hQ
      (fun eta heta => physicalNegativeParameter_analyticAt (hc eta heta) (ha eta heta)
        (hS eta heta) (hamp eta heta))
      (fun eta heta => physicalNegativeParameter_zero (hS eta heta) (he eta heta))
      hB (fun eta heta => div_ne_zero (hS eta heta) (hamp eta heta))
  refine ⟨a,r,C,M,K,haR,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta j n hn
  have hc' : AnalyticAt ℂ (fun t => curve (t,eta)) 0 :=
    (hc eta heta).comp (f := fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)
  have ha' : AnalyticAt ℂ (fun t => amp (t,eta)) 0 :=
    (ha eta heta).comp (f := fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)
  rw [physical_negative_boundary_jet_integral n j hn hc' ha' (hS eta heta)
    (he eta heta) hb (hB eta heta),norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hfac : ‖(((n+1).factorial:ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  apply (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
  have hi := norm_integral_le_of_norm_le
    (integrable_const ((j.factorial:ℝ)*(K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1))/
      (a/((n+1:ℕ):ℝ)^3)^j) : Integrable (fun _q : Fin n→ℝ => _)
        (Measure.pi (fun _ => edgeAngleMeasure)))
    (Filter.Eventually.of_forall (fun q : Fin n→ℝ =>
      hbound eta heta j n hn q 0 (by simp only [norm_zero]; positivity)))
  simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hi

end
end IsingBulk.Joint.Negative
