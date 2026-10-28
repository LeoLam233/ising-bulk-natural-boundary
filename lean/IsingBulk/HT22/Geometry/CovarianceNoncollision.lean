import IsingBulk.HT22.Geometry.CovarianceShell

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators
open Set IsingBulk.Preferred22

/-- On the entire right rectangle the sole collective denominator is
separated away from the full-equality locus. Partial diagonals need no
punctures. Extrema are chosen in this proof, never differentiated. -/
theorem actual_mixed_covariance_noncollision (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ, (∀ a, θ a∈Icc (-d.b-δB) B.delta) →
      (∃ i j, θ i≠θ j) →
      sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
        (actualRegularCoordinates d B ε τ θ)≠0 := by
  obtain ⟨c,e,t,δ,hc,he,ht,hδ,hδB,hbound⟩ := actual_mixed_covariance_shell d B
  refine ⟨e,t,δ,he,ht,hδ,hδB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hnon
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ θ hne
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ θ hne
  have hext (a : Fin N) : θ i≤θ a ∧ θ a≤θ j :=
    ⟨hmin a (Finset.mem_univ _),hmax a (Finset.mem_univ _)⟩
  have hr : 0<θ j-θ i := by
    obtain ⟨u,v,huv⟩ := hnon
    have hui := hext u
    have hvi := hext v
    by_contra hn
    apply huv
    linarith
  have hw (a : Fin N) : θ i+d.b-2*(θ j-θ i)≤θ a+d.b ∧
      θ a+d.b≤θ i+d.b+2*(θ j-θ i) := by
    have ha := hext a
    constructor <;> linarith
  exact (hbound N hN ε τ (θ i+d.b) (θ j-θ i) hε hεr hτ hτr hr θ hθ hw i j hext le_rfl).2.2

end
end IsingBulk.HT22.Geometry
