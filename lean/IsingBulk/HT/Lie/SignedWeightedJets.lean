import IsingBulk.HT.Lie.SignedWeightedIntegral

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Tail IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology

/-- At each fixed positive epsilon, the true parameter jet is integration
against one continuous density jet, common to all bounded measurable weights.
This qualitative representation is used only for finite partition identities. -/
theorem signed_weighted_jet_representation (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ, ∀ n j : ℕ,
      ∃ f : AngularSpace n → ℂ, ContinuousOn f (microcoreCube (n+1) r) ∧
      ∀ w : AngularSpace n → ℝ, Measurable w → support w ⊆ microcoreCube (n+1) r →
      ∀ B : ℝ, 0 ≤ B → (∀ u ∈ microcoreCube (n+1) r, |w u| ≤ B) →
      iteratedDeriv j (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε w) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u in microcoreCube (n+1) r, (w u:ℂ)*f u := by
  obtain ⟨rD,hrD,hdata⟩ := allBranchExterior_original_density_data d
  obtain ⟨a,rS,ha,hrS,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rD rS
  have hr : 0 < r := lt_min hrD hrS
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n j
  let K := microcoreCube (n+1) r
  let s := radialParameter d.theta ε
  let Q := unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)
  let F := signedComplexDensity (Complex.exp (Complex.I*(α:ℂ))) (-d.c₀*ε) d.thetaB Q
  let psi : AngularSpace n → (Fin (n+1) → ℂ) := fun u i => (u i:ℂ)
  have hpsi : Continuous psi := by fun_prop
  have hK : IsCompact K := microcoreCube_compact (n+1) r
  have hv : -d.c₀*ε < 0 := by nlinarith [d.c₀_pos]
  have hd (u : AngularSpace n) (hu : u ∈ K) := hdata ε hε (hεr.trans (min_le_left _ _)) n u
    (fun i => ((mem_microcoreCube r u).mp hu i).trans (min_le_left _ _))
  obtain ⟨U,hU,hs,hdom⟩ := signed_compact_density_domain (Complex.exp (Complex.I*(α:ℂ))) (-d.c₀*ε) d.thetaB Q s K hK
    (fun u hu => (hd u hu).1) (fun u hu => (hd u hu).2)
    (fun u hu => (hgap ε hε (hεr.trans (min_le_right _ _)) α n u
      (fun i => ((mem_microcoreCube r u).mp hu i).trans (min_le_right _ _))).1)
  let f : AngularSpace n → ℂ := fun u => iteratedDeriv j (fun t => F (t,psi u)) s
  have hf : ContinuousOn f K := by
    intro u hu
    have ha := (jointParameterJet_analyticAt (hdom s hs u hu).2 j).continuousAt
    have hc := ha.comp (f := fun u : AngularSpace n => (s,psi u)) (continuous_const.prodMk hpsi).continuousAt
    simpa only [Function.comp_def,f,jointParameterJet_eq,← iteratedDeriv_eq_iterate] using hc.continuousWithinAt
  refine ⟨f,hf,?_⟩
  intro w hw hsupp B hB hb
  have he : signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε w =ᶠ[𝓝 s]
      (fun t => ((n+1).factorial:ℂ)⁻¹*∫ u in K, (w u:ℂ)*F (t,psi u)) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    exact signed_weighted_integral_eq (Complex.exp (Complex.I*(α:ℂ))) d ε hε K hK.measurableSet w hsupp t
      (fun u hu => (hdom t ht u hu).1)
  rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  congr 1
  apply compact_bounded_weight_integral_iteratedDeriv hK hU F psi hpsi
    (fun t ht u hu => (hdom t ht u hu).2) _
    (Complex.measurable_ofReal.comp hw).aestronglyMeasurable hB _ j hs
  filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
  simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hb u hu

end
end IsingBulk.HT.Lie
