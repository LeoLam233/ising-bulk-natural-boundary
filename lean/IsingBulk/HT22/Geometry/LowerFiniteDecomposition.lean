import IsingBulk.HT22.Geometry.LowerLocalizedBounds

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic LocalLimit IsingBulk.Branch
open scoped Topology BigOperators ContDiff

/-- Actual lower finite coefficient decomposition into bounded physical
local integrals and one smooth diameter-separated remainder. All local
radii, charts and arithmetic gaps are constructed from the source. -/
theorem lower_signed_finite_decomposition {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a)) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump d,∀ τ : ℝ,0≤τ →
      ∀ n : ℕ,Odd (n+1) → n+1<p → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∃ P : List ((Fin n → ℝ) → ℝ),∃ rem : (Fin n → ℝ) → ℝ,∃ r : ℝ,
      0<r ∧ ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ) ∧
      (∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))) ∧
      (∀ ψ∈P,∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
        ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ (fun θ => (ψ θ:ℂ)) W))
          (radialParameter d.alpha ε)‖≤C) := by
  classical
  obtain ⟨g,hg,hpartition⟩ := exists_regular_signed_finite_partition hp hp5 ha hp.pos d
    (positive_geometry_branch_identity d negative hcos)
  refine ⟨g,hg,?_⟩
  intro B τ hτ n hodd hnp δB hδB hδ
  let S := regularSignedMeanIndices d B negative (n+1) g
  have hex (l : {l : ℤ // l∈S}) := lower_localized_signed_bound hp hp5 ha d B negative hcos
    n hodd hnp hg hτ l l.2
  choose R hR hbound using hex
  let R' : ℤ → ℝ := fun l => if hl : l∈S then R ⟨l,hl⟩ else 1
  have hR' (l : ℤ) (hl : l∈S) : 0<R' l := by
    simpa only [R',dite_eq_left hl] using hR ⟨l,hl⟩
  obtain ⟨P,rem,r,hr,hsmooth,hlocal,hidentity,hfar⟩ :=
    hpartition B negative n (by omega) δB hδB hδ R' hR'
  refine ⟨P,rem,r,hr,hsmooth,(fun ψ hψ => ⟨(hlocal ψ hψ).1,(hlocal ψ hψ).2.1⟩),hidentity,hfar,?_⟩
  intro ψ hψ W hW j
  obtain ⟨hc,hcomp,l,hl,hs⟩ := hlocal ψ hψ
  apply hbound ⟨l,hl⟩ (fun θ => (ψ θ:ℂ)) (Complex.continuous_ofReal.comp hc.continuous) _ W hW j
  intro θ hθ
  have ht : θ∈tsupport ψ := subset_tsupport ψ (by simpa only [Function.mem_support,Complex.ofReal_ne_zero] using hθ)
  have hh := hs ht
  rw [mem_ball,dist_eq_norm] at hh
  have hlS : l∈S := hl
  simpa only [R',dite_eq_left hlS] using hh


theorem lower_signed_finite_decomposition_germ {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a)) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump d,∀ τ : ℝ,0≤τ →
      ∀ n : ℕ,Odd (n+1) → n+1<p → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∃ P : List ((Fin n → ℝ) → ℝ),∃ rem : (Fin n → ℝ) → ℝ,∃ r : ℝ,
      0<r ∧ ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ) ∧
      (∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB →
        preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))<r →
        rem =ᶠ[𝓝 θ] (fun _ => 0)) ∧
      (∀ ψ∈P,∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
        ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ (fun θ => (ψ θ:ℂ)) W))
          (radialParameter d.alpha ε)‖≤C) := by
  classical
  obtain ⟨g,hg,hpartition⟩ := exists_regular_signed_finite_partition_germ hp hp5 ha hp.pos d
    (positive_geometry_branch_identity d negative hcos)
  refine ⟨g,hg,?_⟩
  intro B τ hτ n hodd hnp δB hδB hδ
  let S := regularSignedMeanIndices d B negative (n+1) g
  have hex (l : {l : ℤ // l∈S}) := lower_localized_signed_bound hp hp5 ha d B negative hcos
    n hodd hnp hg hτ l l.2
  choose R hR hbound using hex
  let R' : ℤ → ℝ := fun l => if hl : l∈S then R ⟨l,hl⟩ else 1
  have hR' (l : ℤ) (hl : l∈S) : 0<R' l := by
    simpa only [R',dite_eq_left hl] using hR ⟨l,hl⟩
  obtain ⟨P,rem,r,hr,hsmooth,hlocal,hidentity,hfar,hgerm⟩ :=
    hpartition B negative n (by omega) δB hδB hδ R' hR'
  refine ⟨P,rem,r,hr,hsmooth,(fun ψ hψ => ⟨(hlocal ψ hψ).1,(hlocal ψ hψ).2.1⟩),hidentity,hfar,hgerm,?_⟩
  intro ψ hψ W hW j
  obtain ⟨hc,hcomp,l,hl,hs⟩ := hlocal ψ hψ
  apply hbound ⟨l,hl⟩ (fun θ => (ψ θ:ℂ)) (Complex.continuous_ofReal.comp hc.continuous) _ W hW j
  intro θ hθ
  have ht : θ∈tsupport ψ := subset_tsupport ψ (by simpa only [Function.mem_support,Complex.ofReal_ne_zero] using hθ)
  have hh := hs ht
  rw [mem_ball,dist_eq_norm] at hh
  have hlS : l∈S := hl
  simpa only [R',dite_eq_left hlS] using hh

end
end IsingBulk.HT22.Geometry
