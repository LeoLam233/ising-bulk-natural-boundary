import IsingBulk.Tail.AllBranchExteriorAnalyticDomain

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology

theorem allBranchExterior_weighted_integral_eq {n : ℕ} (d : LocalBranchData)
    (ε : ℝ) (hε : 0 < ε) (K : Set (AngularSpace n)) (hK : MeasurableSet K)
    (w : AngularSpace n → ℝ) (hsupp : support w ⊆ K) (s : ℂ)
    (hp : ∀ u ∈ K, MicrocoreJetPoint (-d.c₀*ε) d.thetaB s u) :
    allBranchOriginalWeightedIntegral n d ε w s =
      ((n+1).factorial:ℂ)⁻¹*∫ u in K, (w u:ℂ)*
        sourceComplexDensity (-d.c₀*ε) d.thetaB
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
          (realAngularEmbedding (s,u)) := by
  have hv : -d.c₀*ε < 0 := by nlinarith [d.c₀_pos]
  have hz (u : AngularSpace n) (hu : u ∉ K) : w u=0 := by
    by_contra hn
    exact hu (hsupp hn)
  unfold allBranchOriginalWeightedIntegral
  congr 1
  calc
    _ = ∫ u in K, (w u:ℂ)*sourceReducedAngularDensity (Real.exp (-d.c₀*ε)) s
        (fun i => u i-d.thetaB) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hz u hu])).symm
    _ = _ := by
      apply setIntegral_congr_fun hK
      intro u hu
      exact (allBranchExterior_initial_source_identity (-d.c₀*ε) d.thetaB w s u hv
        (hp u hu).g_pos (hp u hu).im_pos).symm

/-- Qualitative fixed-epsilon convergence of the true parameter derivatives.
The compact parameter neighborhood is derived from the actual density, and
is common to the whole sequence of fixed spatial weights. -/
theorem allBranchExterior_weighted_derivatives_tendsto {n : ℕ} (d : LocalBranchData)
    (ε : ℝ) (hε : 0 < ε) (s : ℂ) (K : Set (AngularSpace n)) (hK : IsCompact K)
    (hp : ∀ u ∈ K, MicrocoreJetPoint (-d.c₀*ε) d.thetaB s u)
    (hQ : ∀ u ∈ K, AnalyticAt ℂ
      (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
      (s,chartMap (-d.c₀*ε) d.thetaB s u))
    (w : ℕ → AngularSpace n → ℝ) (wlim : AngularSpace n → ℝ)
    (hw : ∀ k, Measurable (w k)) (hwlim : Measurable wlim)
    (hsupp : ∀ k, support (w k) ⊆ K) (hsupplim : support wlim ⊆ K)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, ∀ᵐ u ∂volume.restrict K, |w k u| ≤ B)
    (hblim : ∀ᵐ u ∂volume.restrict K, |wlim u| ≤ B)
    (hlim : ∀ᵐ u ∂volume.restrict K, Tendsto (fun k => w k u) atTop (𝓝 (wlim u)))
    (j : ℕ) :
    Tendsto (fun k => iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε (w k)) s)
      atTop (𝓝 (iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε wlim) s)) := by
  let Q := unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)
  let F := sourceComplexDensity (-d.c₀*ε) d.thetaB Q
  let psi : AngularSpace n → (Fin (n+1) → ℂ) := fun u i => (u i:ℂ)
  have hv : -d.c₀*ε < 0 := by nlinarith [d.c₀_pos]
  obtain ⟨U,hU,hs,hdata⟩ := allBranchExterior_compact_density_domain (-d.c₀*ε) d.thetaB hv Q s K hK hp hQ
  have hder (v : AngularSpace n → ℝ) (hvK : support v ⊆ K) :
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε v) s =
        ((n+1).factorial:ℂ)⁻¹*iteratedDeriv j (fun t => ∫ u in K, (v u:ℂ)*F (t,psi u)) s := by
    have he : allBranchOriginalWeightedIntegral n d ε v =ᶠ[𝓝 s]
        (fun t => ((n+1).factorial:ℂ)⁻¹*∫ u in K, (v u:ℂ)*F (t,psi u)) := by
      filter_upwards [hU.mem_nhds hs] with t ht
      exact allBranchExterior_weighted_integral_eq d ε hε K hK.measurableSet v hvK t
        (fun u hu => (hdata t ht u hu).1)
    rw [he.iteratedDeriv_eq,iteratedDeriv_const_mul_field]
  have ht := compact_bounded_weight_derivatives_tendsto hK hU F psi
    (show Continuous psi by fun_prop) (fun t ht u hu => (hdata t ht u hu).2)
    (fun k u => (w k u:ℂ)) (fun u => (wlim u:ℂ))
    (fun k => (Complex.measurable_ofReal.comp (hw k)).aestronglyMeasurable)
    (Complex.measurable_ofReal.comp hwlim).aestronglyMeasurable hB
    (fun k => (hb k).mono (fun u hu => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hu))
    (hblim.mono (fun u hu => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hu))
    (hlim.mono (fun u hu => Complex.continuous_ofReal.continuousAt.tendsto.comp hu)) j hs
  have heq : (fun k => iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε (w k)) s) =
      (fun k => ((n+1).factorial:ℂ)⁻¹*iteratedDeriv j (fun t => ∫ u in K, (w k u:ℂ)*F (t,psi u)) s) :=
    funext (fun k => hder (w k) (hsupp k))
  rw [heq,hder wlim hsupplim]
  exact tendsto_const_nhds.mul ht

end
end IsingBulk.Tail
