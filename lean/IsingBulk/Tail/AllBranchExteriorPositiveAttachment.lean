import IsingBulk.Tail.AllBranchExteriorPositiveDiameterIntegral
import IsingBulk.Tail.AllBranchExteriorKernelContinuity
import IsingBulk.Tail.AllBranchExteriorOriginalKernel

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Set MeasureTheory
open scoped BigOperators

theorem allBranchExterior_original_kernel_density_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ ζ r : ℝ, 0 < ζ ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) →
        allBranchExteriorKernelDensity d ε u ≤ 4*allBranchExteriorPositiveKernel d ε (d.c₀*ε) (ζ*ε) u := by
  obtain ⟨ζ,r,hζ,hr,hfloor⟩ := allBranchExterior_original_kernel_floor d hcsmall
  refine ⟨ζ,r,hζ,hr,?_⟩
  intro ε hε hεr n u hu
  have hh := hfloor ε hε hεr n u hu
  rw [original_chartMap_eq] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Finset.prod_nonneg
    (s := Finset.univ) (f := fun i => ‖deriv (originalPhase d ε) (u i)‖) (fun _ _ => norm_nonneg _))
  unfold allBranchExteriorKernelDensity allBranchExteriorPositiveKernel allBranchExteriorTotalPhase originalRealPhase
  convert! hm using 1
  push_cast
  ring

/-- The positive diameter-power estimate is attached to the actual regular
kernel, with every small-radius and kernel-floor input derived internally. -/
theorem allBranchExterior_positive_weighted_density_integral {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ ζ r : ℝ, 0 < ζ ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ,
      ∀ R a D : ℝ, 0 ≤ R → R ≤ r → 0 < a → 0 < D →
      B.original.separationThreshold*ε ≤ a → 2*B.original.C₀*ε ≤ a → ∀ P : ℕ,
      let S := @allBranchExteriorPositiveDiameterRegion (n+1) R a D
      IntegrableOn (fun u => allBranchExteriorDiameter u^(P+1)*allBranchExteriorKernelDensity d ε u) S ∧
      (∫ u in S, allBranchExteriorDiameter u^(P+1)*allBranchExteriorKernelDensity d ε u) ≤
        4*((n+1:ℝ)^2*((D^(P+1)*allBranchExteriorPositiveCost B a D)*
          (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*
            ((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (ζ*ε)|))*B.lengthC^((n+1)-2)))) := by
  obtain ⟨ζ,rK,hζ,hrK,hfloor⟩ := allBranchExterior_original_kernel_density_bound d hcsmall
  obtain ⟨rC,hrC,hchart⟩ := original_microcore_chart d
  let R₀ := min rK (min rC (min B.r (min B.ε₀ (min Real.pi (min d.c₀⁻¹ ζ⁻¹)))))
  have hR₀ : 0 < R₀ := lt_min hrK (lt_min hrC (lt_min B.r_pos (lt_min B.ε₀_pos
    (lt_min Real.pi_pos (lt_min (inv_pos.mpr d.c₀_pos) (inv_pos.mpr hζ))))))
  let r := R₀/2
  have hr : 0 < r := half_pos hR₀
  have hs : r < rK ∧ r < rC ∧ r < B.r ∧ r < B.ε₀ ∧ r < Real.pi ∧ r < d.c₀⁻¹ ∧ r < ζ⁻¹ := by
    have hh : r < R₀ := half_lt_self hR₀
    simpa only [R₀,lt_min_iff] using hh
  refine ⟨ζ,r,hζ,hr,?_⟩
  intro ε hε hεr n R a D hR hRr ha hD hsmall₁ hsmall₂ P
  dsimp only
  let S := @allBranchExteriorPositiveDiameterRegion (n+1) R a D
  let box := Icc (fun _ : Fin (n+1) => -R) (fun _ => R)
  have hsub : S ⊆ box := by
    intro u hu
    exact ⟨fun i => by linarith [hu.1.1 i],hu.1.2⟩
  have hhp (u : AngularSpace n) (hu : u ∈ box) :
      MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u :=
    hchart ε hε (hεr.trans_lt hs.2.1) n u
      (fun i => (abs_le.mpr ⟨hu.1 i,hu.2 i⟩).trans_lt (hRr.trans_lt hs.2.1))
  have hα1 : d.c₀*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hεr.trans hs.2.2.2.2.2.1.le) d.c₀_pos.le
    rwa [mul_inv_cancel₀ d.c₀_pos.ne'] at hh
  have hβ1 : ζ*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hεr.trans hs.2.2.2.2.2.2.le) hζ.le
    rwa [mul_inv_cancel₀ hζ.ne'] at hh
  have hK := allBranchExterior_positive_diameter_integral (N := n+1) B ε a D R (d.c₀*ε) (ζ*ε) P
    hε (hεr.trans hs.2.2.2.1.le) ha hD hsmall₁ hsmall₂ hR (hRr.trans hs.2.2.1.le)
    (hRr.trans hs.2.2.2.2.1.le) (mul_pos d.c₀_pos hε) hα1 (mul_pos hζ hε) hβ1
  have hi : IntegrableOn (fun u => allBranchExteriorDiameter u^(P+1)*allBranchExteriorKernelDensity d ε u) S :=
    (((@allBranchExterior_diameter_continuous (n+1)).pow (P+1)).continuousOn.mul
      (allBranchExterior_kernel_density_continuousOn d hε box hhp)).integrableOn_compact isCompact_Icc |>.mono_set hsub
  have hp (u : AngularSpace n) (hu : u ∈ S) :
      allBranchExteriorDiameter u^(P+1)*allBranchExteriorKernelDensity d ε u ≤
        4*(allBranchExteriorDiameter u^(P+1)*allBranchExteriorPositiveKernel d ε (d.c₀*ε) (ζ*ε) u) := by
    have hh := mul_le_mul_of_nonneg_left
      (hfloor ε hε (hεr.trans hs.1.le) n u
        (fun i => (abs_le.mpr ⟨(hsub hu).1 i,(hsub hu).2 i⟩).trans (hRr.trans hs.1.le)))
      (pow_nonneg (allBranchExterior_diameter_nonneg u) (P+1))
    nlinarith
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ u in S, 4*(allBranchExteriorDiameter u^(P+1)*allBranchExteriorPositiveKernel d ε (d.c₀*ε) (ζ*ε) u) :=
      setIntegral_mono_on hi (hK.1.const_mul 4) (allBranchExterior_positive_diameter_region_measurable R a D) hp
    _ = 4*(∫ u in S, allBranchExteriorDiameter u^(P+1)*allBranchExteriorPositiveKernel d ε (d.c₀*ε) (ζ*ε) u) :=
      integral_const_mul _ _
    _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using mul_le_mul_of_nonneg_left hK.2 (by norm_num : (0:ℝ) ≤ 4)

end
end IsingBulk.Tail
