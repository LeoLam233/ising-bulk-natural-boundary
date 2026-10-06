import IsingBulk.Tail.AllBranchExteriorKernelContinuity

/-! Integral bounds for the genuine regular kernel on negative-coordinate cells.
The microcore chart premise is internal geometric data, supplied by
`original_microcore_chart` on a radius preceding the particle number. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Filter
open scoped BigOperators

theorem allBranchExterior_negative_integral_bounds {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ ε R a : ℝ,
      0 < ε → ε ≤ B.ε₀ → 0 ≤ R → R ≤ B.r → R ≤ Real.pi → d.c₀*ε ≤ 1 → 0 < a →
      (∀ u : AngularSpace n, u ∈ Icc (fun _ => -R) (fun _ => R) →
        MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) →
      ∀ p q v : Fin (n+1), p ≠ q → ∀ S : Set (AngularSpace n), MeasurableSet S →
      S ⊆ Icc (fun _ => -R) (fun _ => R) →
      (∀ u ∈ S, a ≤ |u p| ∧ u v ≤ 0) →
      IntegrableOn (allBranchExteriorKernelDensity d ε) S ∧
      (p ≠ v → (∫ u in S, allBranchExteriorKernelDensity d ε u) ≤
        (2*(B.magnitudeUpper/Real.sqrt a)*C)*
        (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*
          (2*Real.log ((R+ε)/ε))*B.lengthC^((n+1)-2))) ∧
      (∀ δ : ℝ, 0 < δ → (∀ u ∈ S, δ ≤ |u v|) →
        (∫ u in S, allBranchExteriorKernelDensity d ε u) ≤
          (2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt δ))*
          (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*B.lengthC^((n+1)-1))) := by
  obtain ⟨c,C,hc,hC,hpoint⟩ := allBranchExterior_negative_density_bounds B
  refine ⟨c,C,hc,hC,?_⟩
  intro n ε R a hε hεr hR hRB hRπ hα1 ha hchart p q v hpq S hS hsub hgeom
  let box := Icc (fun _ : Fin (n+1) => -R) (fun _ => R)
  have hα : 0 < d.c₀*ε := mul_pos d.c₀_pos hε
  have hKbox : IntegrableOn (allBranchExteriorKernelDensity d ε) box :=
    (allBranchExterior_kernel_density_continuousOn d hε box hchart).integrableOn_compact isCompact_Icc
  have hKS := hKbox.mono_set hsub
  have hbound (u : AngularSpace n) (hu : u ∈ S) := hpoint n ε a hε hεr ha u
    (fun i => (abs_le.mpr ⟨(hsub hu).1 i,(hsub hu).2 i⟩).trans hRB)
    (hchart u (hsub hu)) p v (hgeom u hu).1 (hgeom u hu).2
  have hA : 0 ≤ B.magnitudeUpper/Real.sqrt a :=
    div_nonneg B.magnitudeUpper_pos.le (Real.sqrt_nonneg a)
  refine ⟨hKS,?_,?_⟩
  · intro hpv
    have hlog := allBranchExterior_log_phase_integral B p v hpv hε hεr hR hRB hRπ hα hα1
    let K := allBranchExteriorLogPhaseKernel d ε (d.c₀*ε) p v
    let A := 2*(B.magnitudeUpper/Real.sqrt a)*C
    have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) hA) hC.le
    have hK0 (u : AngularSpace n) : 0 ≤ K u := by
      unfold K allBranchExteriorLogPhaseKernel
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (inv_nonneg.mpr (by positivity))) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    calc
      _ ≤ ∫ u in S, A*K u := setIntegral_mono_on hKS ((hlog.1.mono_set hsub).const_mul A) hS
        (fun u hu => (hbound u hu).1 hpv)
      _ = A*(∫ u in S, K u) := integral_const_mul _ _
      _ ≤ A*(∫ u in box, K u) := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hlog.1 (Eventually.of_forall hK0) (Eventually.of_forall hsub)) hA0
      _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using mul_le_mul_of_nonneg_left hlog.2 hA0
  · intro δ hδ hδS
    have hone := allBranchExterior_one_phase_integral B p q hpq hε hεr hR hRB hRπ hα hα1
    let K := allBranchExteriorOnePhaseKernel d ε (d.c₀*ε) p
    let A := 2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt δ)
    have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (by norm_num) hA)
      (mul_nonneg hc.le (Real.sqrt_nonneg δ))
    have hK0 (u : AngularSpace n) : 0 ≤ K u := by
      unfold K allBranchExteriorOnePhaseKernel
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    calc
      _ ≤ ∫ u in S, A*K u := setIntegral_mono_on hKS ((hone.1.mono_set hsub).const_mul A) hS
        (fun u hu => (hbound u hu).2 δ hδ (hδS u hu))
      _ = A*(∫ u in S, K u) := integral_const_mul _ _
      _ ≤ A*(∫ u in box, K u) := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hone.1 (Eventually.of_forall hK0) (Eventually.of_forall hsub)) hA0
      _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using mul_le_mul_of_nonneg_left hone.2 hA0

end
end IsingBulk.Tail
