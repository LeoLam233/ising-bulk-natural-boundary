import IsingBulk.HT22.Geometry.FirstCenterPartition
import IsingBulk.HT22.Geometry.LowerLocalizedBounds

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic LocalLimit IsingBulk.Branch
open scoped Topology BigOperators ContDiff

/-- First-order source decomposition with one untouched critical cutoff,
only bounded noncritical local pieces, and a global-germ-zero near-diagonal
remainder. The critical radius is free for the actual FIRST chart theorem. -/
theorem first_signed_finite_decomposition {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a)) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump d,∀ τ : ℝ,0≤τ →
      ∀ n : ℕ,n+1=p → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∀ l₀ : ℤ,signedEqualityMean negative (n+1) l₀= -d.alpha →
      ∀ R₀ : ℝ,0<R₀ →
      ∃ χ₀ : (Fin n → ℝ) → ℝ,∃ P : List ((Fin n → ℝ) → ℝ),
      ∃ rem : (Fin n → ℝ) → ℝ,∃ r : ℝ,0<r ∧
      ContDiff ℝ ∞ χ₀ ∧ HasCompactSupport χ₀ ∧ (∀ θ,0≤χ₀ θ ∧ χ₀ θ≤1) ∧
      tsupport χ₀⊆ball (fun _ => -d.alpha) R₀ ∧ χ₀ =ᶠ[𝓝 (fun _ => -d.alpha)] (fun _ => 1) ∧
      ContDiff ℝ ∞ rem ∧ (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ) ∧
      (∀ θ,χ₀ θ+(P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB →
        preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))<r → rem =ᶠ[𝓝 θ] (fun _ => 0)) ∧
      (∀ ψ∈P,∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
        ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ (fun θ => (ψ θ:ℂ)) W))
          (radialParameter d.alpha ε)‖≤C) := by
  classical
  obtain ⟨g,hg,hcover⟩ := finite_signed_regular_center_cover hp hp5 ha hp.pos d
    (positive_geometry_branch_identity d negative hcos)
  refine ⟨g,hg,?_⟩
  intro B τ hτ n hn δB hδB hδ l₀ hcrit R₀ hR₀
  let S := regularSignedMeanIndices d B negative (n+1) g
  let center (l : ℤ) : Fin n → ℝ := fun _ => signedEqualityMean negative (n+1) l
  have hex (l : {l : ℤ // l∈S.erase l₀}) := first_other_localized_signed_bound hp hp5 ha d B negative hcos
    n hn hg hτ l (Finset.mem_of_mem_erase l.2) (by
      intro he
      have hh := (signedEqualityMean_injective negative (by omega : 0<n+1)) (he.trans hcrit.symm)
      exact (Finset.mem_erase.mp l.2).1 hh)
  choose R hR hbound using hex
  let R' : ℤ → ℝ := fun l => if hl : l∈S.erase l₀ then R ⟨l,hl⟩ else 1
  have hR' (l : ℤ) (hl : l∈S.erase l₀) : 0<R' l := by
    simpa only [R',dite_eq_left hl] using hR ⟨l,hl⟩
  obtain ⟨χ₀,P,rem,ρ,hρ,hχ,hχcomp,hχrange,hχsupp,hχone,hsmooth,hlocal,hid,hzero,hgerm⟩ :=
    finite_center_partition_with_first S l₀ center R' R₀ hR₀ hR'
  let r := min ρ (g/4)
  have hr : 0<r := lt_min hρ (by positivity)
  have hlocalWindow (θ : Fin n → ℝ) (hθ : θ∈signedRightRegion (Physical.constraintAngle negative) d B δB)
      (hD : preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))≤r) :
      ∃ l∈S,‖θ-center l‖≤preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ)) := by
    obtain ⟨l,hl,hreg,hs,hw⟩ := hcover B negative n hn.le δB hδB hδ θ hθ (hD.trans (min_le_right _ _))
    refine ⟨l,Finset.mem_filter.mpr ⟨hl,hreg⟩,?_⟩
    apply (pi_norm_le_iff_of_nonneg Metric.diam_nonneg).mpr
    intro j
    have hh := hw j.castSucc
    rw [signed_lift_free_eq_of_right d B hδB (Physical.constraintAngle negative) θ hθ.1 hθ.2 j] at hh
    simpa only [Pi.sub_apply,Real.norm_eq_abs,center,preferredAngularDiameter] using hh
  refine ⟨χ₀,P,rem,r,hr,hχ,hχcomp,hχrange,?_,?_,hsmooth,
    (fun ψ hψ => ⟨(hlocal ψ hψ).1,(hlocal ψ hψ).2.1⟩),hid,?_,?_,?_⟩
  · simpa only [center,hcrit] using hχsupp
  · simpa only [center,hcrit] using hχone
  · intro θ hθ hrem
    by_contra hh
    obtain ⟨l,hl,hwin⟩ := hlocalWindow θ hθ (le_of_not_gt hh)
    exact hrem (hzero l hl θ (hwin.trans ((le_of_not_gt hh).trans (min_le_left _ _))))
  · intro θ hθ hD
    obtain ⟨l,hl,hwin⟩ := hlocalWindow θ hθ hD.le
    exact hgerm l hl θ (hwin.trans_lt (hD.trans_le (min_le_left _ _)))
  · intro ψ hψ W hW j
    obtain ⟨hc,hcomp,l,hl,hs⟩ := hlocal ψ hψ
    apply hbound ⟨l,hl⟩ (fun θ => (ψ θ:ℂ)) (Complex.continuous_ofReal.comp hc.continuous) _ W hW j
    intro θ hθ
    have ht : θ∈tsupport ψ := subset_tsupport ψ (by simpa only [Function.mem_support,Complex.ofReal_ne_zero] using hθ)
    have hh := hs ht
    rw [mem_ball,dist_eq_norm] at hh
    have hlS : l∈S.erase l₀ := hl
    simpa only [R',dite_eq_left hlS,center] using hh

end
end IsingBulk.HT22.Geometry
