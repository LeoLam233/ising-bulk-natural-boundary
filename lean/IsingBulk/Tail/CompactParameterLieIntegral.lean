import IsingBulk.Tail.SourceJetIntegralTheorem

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology ContDiff

/-- A fixed compact angular support constructs its own common parameter
neighborhood. Flux vanishing follows from smooth compact support. -/
theorem compact_parameter_lie_integral {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i)) (hA : ParameterSmoothOn Ω A)
    {K : Set (AngularSpace n)} (hK : IsCompact K)
    (hsupp : ∀ s, support (A s) ⊆ K) {s : ℂ} (hs : ∀ x ∈ K, (s,x) ∈ Ω) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x, A t x) s = ∫ x, ((lieStep V)^[j] A) s x := by
  have hevent : ∀ᶠ t in 𝓝 s, ∀ x ∈ K, (t,x) ∈ Ω :=
    hK.eventually_forall_of_forall_eventually (fun x hx => hΩ.mem_nhds (hs x hx))
  obtain ⟨U,hUsub,hU,hsU⟩ := mem_nhds_iff.mp hevent
  have hstage (k : ℕ) := hA.iterate_lieStep hΩ V A hV k
  have hsiter (k : ℕ) (t : ℂ) (ht : t ∈ U) : tsupport (((lieStep V)^[k] A) t) ⊆ K :=
    iterate_lieStep_support_subset V A hU hK.isClosed (fun t _ => hsupp t) k t ht
  have hflux (k : ℕ) (t : ℂ) (ht : t ∈ U) (i : Fin (n+1)) :
      ContDiff ℝ 1 (fun x => V t x i*((lieStep V)^[k] A) t x) := by
    have hsupport : tsupport (fun x => V t x i*((lieStep V)^[k] A) t x) ⊆ K :=
      tsupport_mul_subset_right.trans (hsiter k t ht)
    apply (contDiff_of_closed_support _ hsupport _).of_le (by simp)
    intro x hx
    have hz := hUsub ht x hx
    exact ((hV i (t,x) hz).1.comp x (contDiffAt_const.prodMk contDiffAt_id)).mul
      ((hstage k (t,x) hz).1.comp x (contDiffAt_const.prodMk contDiffAt_id))
  have hid := compact_support_iterate_lieStep_integral_on hK hU V A j
    (fun k _ t ht => subset_closure.trans (hsiter k t ht))
    (fun k _ z hz => (hstage k z (hUsub hz.1 z.2 hz.2)).1.continuousAt.continuousWithinAt)
    (fun k _ z hz => ((hstage k).paramDeriv hΩ z (hUsub hz.1 z.2 hz.2)).1.continuousAt.continuousWithinAt)
    (fun k _ t ht x hx => (hstage k (t,x) (hUsub ht x hx)).2)
    (fun k _ t ht i => hflux k t ht i)
  simpa only [iteratedDeriv_eq_iterate] using (hid hsU).symm

end
end IsingBulk.Tail
