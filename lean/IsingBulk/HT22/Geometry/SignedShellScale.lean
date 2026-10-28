import IsingBulk.HT22.Geometry.SignedShellIntegration

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory IsingBulk.Preferred22

/-- Exact N−3 geometric cost of the signed shell integration. Here
N=m+3, so the N−2 independent non-extreme factors number m+1, while
the integrated extreme pair contributes Δ⁻¹. The scalar density f can
be the actual new transported density; no old transport is present. -/
theorem signed_shell_scale_lintegral (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0<A ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ η : ℝ, ∀ m : ℕ, ∀ ε τ c r δB K : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      0<r → 0<δB → δB≤δ₀ → 0≤K → ∀ i j : Fin (m+3),
      ∀ f : (Fin (m+3) → ℝ) → ℝ,
      (∀ x : Fin (m+2) → ℝ, constrainedAtTotal c x∈preferredFullRightShell d B δB r i j →
        f (constrainedAtTotal c x)≤K*signedJacobianResolvent η d B ε τ (constrainedAtTotal c x)) →
      (∫⁻ x : Fin (m+2) → ℝ,(preferredFullRightShell d B δB r i j).indicator
        (fun w => ENNReal.ofReal (f w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (K*C*((m+3:ℕ):ℝ)*A^(m+1)*
        (r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε))^m*(1+|Real.log ε|)) := by
  obtain ⟨A,C,e,t,δ,hA,hC,he,ht,hδ,hδB,hbound⟩ := signed_shell_q20_lintegral d B
  refine ⟨32*A,C,e,t,δ,by positivity,hC,he,ht,hδ,hδB,?_⟩
  intro η m ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hpoint
  have hh := hbound η (m+1) ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hpoint
  have hT : 0 < |d.b+c/((m+3:ℕ):ℝ)|+r+ε := by positivity
  have hs : Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε)≠0 := (Real.sqrt_pos.mpr hT).ne'
  convert hh using 1
  congr 1
  rw [show (m+1+2:ℕ)=m+3 by omega]
  rw [show 32*r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε)=
    32*(r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε)) by ring]
  simp only [mul_pow]
  rw [show (r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε))^(m+1)=
    (r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε))^m*
      (r/Real.sqrt (|d.b+c/((m+3:ℕ):ℝ)|+r+ε)) from pow_succ _ m]
  field_simp [hr.ne',hs]

end
end IsingBulk.HT22.Geometry
