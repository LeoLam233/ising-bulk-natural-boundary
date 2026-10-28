import IsingBulk.HT22.Physical.FiniteAssembly.LocalizedPartition
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Physical IsingBulk.HT22.Physical.FiniteAssembly
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem right_log_bound_of_local_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (P : List ((Fin n → ℝ) → ℝ))
    (rem : (Fin n → ℝ) → ℝ) (hP : ∀ ψ∈P,Continuous ψ) (hrem : Continuous rem)
    (hpartition : ∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1) (j : ℕ)
    (hlocal : ∀ ψ∈P,∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C)
    (hR : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r rem)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|)) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|) := by
  obtain ⟨CR,eR,hCR,heR,hR⟩ := hR
  let L := P.map (fun ψ ε => iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ)
    (IsingBulk.Branch.radialParameter d.alpha ε))
  refine finite_plus_log_bound _ _ L ?_ hCR heR hR ?_
  · intro f hf
    obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hf
    exact hlocal ψ hψ
  · intro ε hε _
    simpa only [L,List.map_map,Function.comp_def] using
      actual_right_local_derivative_partition negative n d B hτ r hr P rem hP hrem hpartition
        (preferredRadialTrace_im_pos d hε) j

theorem localized_bound_from_lifted (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (r : ℝ → ℝ)
    (hr : Function.Periodic r (2*Real.pi)) (ψ : (Fin n → ℝ) → ℝ) (j : ℕ)
    (hbound : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖(deriv^[j] (Geometry.localizedSignedLiftedIntegral n negative d B τ (fun θ => (ψ θ:ℂ))
        (rightContourWeight n τ B.p B.m r))) (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  have he : localizedRightIntegral negative n τ B.p B.m r ψ=
      Geometry.localizedSignedLiftedIntegral n negative d B τ (fun θ => (ψ θ:ℂ))
        (rightContourWeight n τ B.p B.m r) :=
    funext (localizedRightIntegral_eq_lifted negative n d B τ r hr ψ)
  simpa only [he,iteratedDeriv_eq_iterate] using hbound
end
end IsingBulk.HT22.Finite
