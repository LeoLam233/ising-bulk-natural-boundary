import IsingBulk.Tail.AllBranchExteriorWeightedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology

/-- At each fixed positive epsilon, the true parameter jet is integration
against one continuous density jet, common to all bounded measurable weights.
This qualitative representation is used only for finite partition identities. -/
theorem allBranchExterior_weighted_jet_representation (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n j : ℕ,
      ∃ f : AngularSpace n → ℂ, ContinuousOn f (microcoreCube (n+1) r) ∧
      ∀ w : AngularSpace n → ℝ, Measurable w → support w ⊆ microcoreCube (n+1) r →
      ∀ B : ℝ, 0 ≤ B → (∀ u ∈ microcoreCube (n+1) r, |w u| ≤ B) →
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε w) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u in microcoreCube (n+1) r, (w u:ℂ)*f u := by
  obtain ⟨r,hr,hdata⟩ := allBranchExterior_original_density_data d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n j
  let K := microcoreCube (n+1) r
  let s := radialParameter d.theta ε
  let Q := unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)
  let F := sourceComplexDensity (-d.c₀*ε) d.thetaB Q
  let psi : AngularSpace n → (Fin (n+1) → ℂ) := fun u i => (u i:ℂ)
  have hpsi : Continuous psi := by fun_prop
  have hK : IsCompact K := microcoreCube_compact (n+1) r
  have hv : -d.c₀*ε < 0 := by nlinarith [d.c₀_pos]
  have hd (u : AngularSpace n) (hu : u ∈ K) := hdata ε hε hεr n u ((mem_microcoreCube r u).mp hu)
  obtain ⟨U,hU,hs,hdom⟩ := allBranchExterior_compact_density_domain (-d.c₀*ε) d.thetaB hv Q s K hK
    (fun u hu => (hd u hu).1) (fun u hu => (hd u hu).2)
  let f : AngularSpace n → ℂ := fun u => iteratedDeriv j (fun t => F (t,psi u)) s
  have hf : ContinuousOn f K := by
    intro u hu
    have ha := (jointParameterJet_analyticAt (hdom s hs u hu).2 j).continuousAt
    have hc := ha.comp (f := fun u : AngularSpace n => (s,psi u)) (continuous_const.prodMk hpsi).continuousAt
    simpa only [Function.comp_def,f,jointParameterJet_eq,← iteratedDeriv_eq_iterate] using hc.continuousWithinAt
  refine ⟨f,hf,?_⟩
  intro w hw hsupp B hB hb
  have he : allBranchOriginalWeightedIntegral n d ε w =ᶠ[𝓝 s]
      (fun t => ((n+1).factorial:ℂ)⁻¹*∫ u in K, (w u:ℂ)*F (t,psi u)) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    exact allBranchExterior_weighted_integral_eq d ε hε K hK.measurableSet w hsupp t
      (fun u hu => (hdom t ht u hu).1)
  rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  congr 1
  apply compact_bounded_weight_integral_iteratedDeriv hK hU F psi hpsi
    (fun t ht u hu => (hdom t ht u hu).2) _
    (Complex.measurable_ofReal.comp hw).aestronglyMeasurable hB _ j hs
  filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
  simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hb u hu

end
end IsingBulk.Tail
