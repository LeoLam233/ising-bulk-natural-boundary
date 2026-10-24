import IsingBulk.Anisotropic.NegativeDominance.PrimitivePhaseGap
import IsingBulk.Anisotropic.NegativeDominance.ProductAngularVariation
import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryGap

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- All nonresonant orders share one positive gap on the entire angular cube.
The inner phase separation and the outer modulus loss are both derived. -/
theorem nonresonant_boundary_product_gap {b : ℝ} {B : ℂ} {p : ℕ}
    (hb : |b|<1) (hB : 0<B.im) (hp : 2≤p) (hphase : IsPrimitiveRoot (continuedRoot (b : ℂ)) p) :
    ∃κ : ℝ,0<κ ∧ ∀N : ℕ,¬p∣N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) → κ≤‖1-∏i,edgeRoot b B (q i)‖ := by
  obtain ⟨κ,hκ,hphasegap⟩ := primitiveRoot_uniform_power_gap hp hphase
  obtain ⟨K,hK,hvariation⟩ := edgeRoot_product_angular_variation hb hB
  let σ := κ/(2*K)
  have hσ : 0<σ := by dsimp [σ]; positivity
  obtain ⟨κout,hκout,houter⟩ := outer_boundary_product_gap hb hB σ hσ
  refine ⟨min κout (κ/2),lt_min hκout (by positivity),?_⟩
  intro N hN q hq
  by_cases hS : σ≤∑i,(q i)^2
  · exact (min_le_left _ _).trans (houter N q hq hS)
  · have hv := (hvariation N q).trans (mul_le_mul_of_nonneg_left (le_of_not_ge hS) hK.le)
    have he : K*σ=κ/2 := by dsimp [σ]; field_simp
    rw [he] at hv
    have htri := norm_add_le (1-∏i,edgeRoot b B (q i))
      ((∏i,edgeRoot b B (q i))-continuedRoot (b : ℂ)^N)
    rw [show (1-∏i,edgeRoot b B (q i))+((∏i,edgeRoot b B (q i))-continuedRoot (b : ℂ)^N)=
      1-continuedRoot (b : ℂ)^N by ring] at htri
    exact (min_le_right _ _).trans (by linarith [hphasegap N hN])

/-- Specialization to the actual dense prime negative-edge phases. -/
theorem prime_negative_boundary_product_gap {B : ℂ} {p k : ℕ}
    (hp : p.Prime) (hk : 0<k) (hkp : 2*k<p)
    (hb : |Real.cos (primePhase p k)|<1) (hB : 0<B.im) :
    ∃κ : ℝ,0<κ ∧ ∀N : ℕ,¬p∣N → ∀q : Fin N→ℝ,
      (∀i,q i∈Icc (-Real.pi) Real.pi) →
      κ≤‖1-∏i,edgeRoot (Real.cos (primePhase p k)) B (q i)‖ := by
  apply nonresonant_boundary_product_gap hb hB hp.two_le
  rw [continuedRoot_primePhase hp hk hkp]
  exact primePhaseRoot_isPrimitiveRoot hp hk (by omega)

end
end IsingBulk.Anisotropic.NegativeDominance
