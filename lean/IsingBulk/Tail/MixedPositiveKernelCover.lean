import IsingBulk.Tail.MixedPositiveSourceIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology

theorem mixed_original_positive_kernel_cover (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α outer B : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (ho : 0<outer) (hB : 0≤B) :
    ∃ (R a e : ℝ) (T : Finset (ℝ×ℝ)),0<R ∧ 0<a ∧ 0<e ∧
      (∀ x∈Icc 0 (2*Real.pi),outer/2≤|sectorDisplacement d.thetaB x| → ∃ I∈T,x∈Icc I.1 I.2) ∧
      ∀ (N : ℕ) (j q : Fin N),j≠q → ∀ I∈T,∀ eps τ : ℝ,0<eps → eps<e →
      let S := mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
      IntegrableOn (mixedPositiveKernelMajorant d η α B eps τ 0 j q) S ∧
      (∫ θ in S,mixedPositiveKernelMajorant d η α B eps τ 0 j q θ)≤
        mixedPositiveIntegralBudget N (d.c₀*eps) (a*eps) (2*Real.pi+4*B*Real.sqrt (2*Real.pi)) := by
  obtain ⟨T,hGap,hCover⟩ := mixed_original_anchor_cover d.thetaB outer ho
  obtain ⟨R,t₀,hR,ht,hIntegral⟩ := mixed_positive_source_cell_integral d hcsmall η α (outer/2) B
    hη hηsmall hα (half_pos ho) hB
  obtain ⟨a,e,ha,he,hIntegral⟩ := hIntegral 0 le_rfl ht
  refine ⟨R,a,e,T,hR,ha,he,hCover,?_⟩
  intro N j q hjq I hI eps τ heps hepslt
  have hh := hIntegral N j q I hjq (fun x hx => by have hg := hGap I hI x hx; linarith)
    eps 0 heps hepslt le_rfl zero_le_one (Or.inl rfl)
  have heq : mixedPositiveKernelMajorant d η α B eps τ 0 j q=
      mixedPositiveKernelMajorant d η α B eps 0 0 j q := by
    funext θ
    simp only [mixedPositiveKernelMajorant,mixedSimpleKernel,deformedPoint_zero]
  dsimp only
  rw [heq]
  exact hh

theorem mixed_current_positive_kernel_cover (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α B : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α)
    (hαsmall : α<Real.sin d.thetaB/4) (hB : 0≤B) :
    ∃ (R t₀ : ℝ) (T : Finset (ℝ×ℝ)),0<R ∧ 0<t₀ ∧
      (∀ x∈Icc 0 (2*Real.pi),α≤Real.sin x → Real.sin x≤3*α/2 → ∃ I∈T,x∈Icc I.1 I.2) ∧
      ∀ τ : ℝ,0≤τ → τ<t₀ → ∃ a e : ℝ,0<a ∧ 0<e ∧
      ∀ (N : ℕ) (j q : Fin N),j≠q → ∀ I∈T,∀ eps lam : ℝ,
      0<eps → eps<e → 0≤lam → lam≤1 →
      let S := mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
      IntegrableOn (mixedPositiveKernelMajorant d η α B eps τ lam j q) S ∧
      (∫ θ in S,mixedPositiveKernelMajorant d η α B eps τ lam j q θ)≤
        mixedPositiveIntegralBudget N (d.c₀*eps) (a*eps) (2*Real.pi+4*B*Real.sqrt (2*Real.pi)) := by
  obtain ⟨T,hGap,hCover⟩ := mixed_current_anchor_cover d.a_pos hα hαsmall
  obtain ⟨R,t₀,hR,ht,hIntegral⟩ := mixed_positive_source_cell_integral d hcsmall η α
    ((Real.sin d.thetaB)^2/4) B hη hηsmall hα (by positivity [d.a_pos]) hB
  refine ⟨R,t₀,T,hR,ht,hCover,?_⟩
  intro τ hτ hτlt
  obtain ⟨a,e,ha,he,hIntegral⟩ := hIntegral τ hτ hτlt
  refine ⟨a,e,ha,he,?_⟩
  intro N j q hjq I hI eps lam heps hepslt hl0 hl1
  exact hIntegral N j q I hjq (fun x hx => by have hg := (hGap I hI x hx).2; linarith)
    eps lam heps hepslt hl0 hl1 (Or.inr (fun x hx => (hGap I hI x hx).1))

end
end IsingBulk.Tail
