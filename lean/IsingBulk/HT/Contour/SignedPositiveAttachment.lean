import IsingBulk.HT.Contour.SignedPositiveDiameter
import IsingBulk.HT.Lie.SignedBranchKernel
import IsingBulk.HT.Lie.SignedKernelDensity

/-! Signed positive-sector spectator integration attached to the literal
original kernel density. The two phase translations are opposite; neither
alters the period counts, Jacobian cost or full spectator arclength product. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

 theorem signed_original_kernel_density_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ ζ r : ℝ, 0 < ζ ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ shift : ℝ, ∀ n : ℕ, ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) →
        signedRegularKernel (Complex.exp (Complex.I*(shift:ℂ))) (radialParameter d.theta ε)
          (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) ≠ 0 ∧
        signedExteriorKernelDensity (Complex.exp (Complex.I*(shift:ℂ))) d ε u ≤
          4*signedPositiveKernel d ε (d.c₀*ε) (ζ*ε) shift (-shift) u := by
  obtain ⟨ζ,r,hζ,hr,hfloor⟩ := signed_original_kernel_gap_and_floor d hcsmall
  refine ⟨ζ,r,hζ,hr,?_⟩
  intro ε hε hεr shift n u hu
  have hh := hfloor ε hε hεr shift n u hu
  refine ⟨hh.1,?_⟩
  have hb := hh.2
  rw [original_chartMap_eq] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg
    (s := Finset.univ) (f := fun i => ‖deriv (originalPhase d ε) (u i)‖) (fun _ _ => norm_nonneg _))
  unfold signedExteriorKernelDensity signedPositiveKernel allBranchExteriorTotalPhase originalRealPhase
  convert! hm using 1
  push_cast
  ring

/-- Full N-dimensional positive diameter estimate for the actual signed
kernel. Every constant is fixed before the phase sign, particle number,
angular radius and collision power. The signed kernel gap is constructed,
not an assumption in this endpoint. -/
theorem signed_allBranchExterior_positive_weighted_density_integral {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ ζ r : ℝ, 0 < ζ ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ shift : ℝ, ∀ n : ℕ,
      ∀ R a D : ℝ, 0 ≤ R → R ≤ r → 0 < a → 0 < D →
      B.original.separationThreshold*ε ≤ a → 2*B.original.C₀*ε ≤ a → ∀ P : ℕ,
      let S := @allBranchExteriorPositiveDiameterRegion (n+1) R a D
      IntegrableOn (fun u => allBranchExteriorDiameter u^(P+1)*
        signedExteriorKernelDensity (Complex.exp (Complex.I*(shift:ℂ))) d ε u) S ∧
      (∫ u in S, allBranchExteriorDiameter u^(P+1)*
        signedExteriorKernelDensity (Complex.exp (Complex.I*(shift:ℂ))) d ε u) ≤
        4*((n+1:ℝ)^2*((D^(P+1)*allBranchExteriorPositiveCost B a D)*
          (((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (d.c₀*ε)|))*
            ((n+1:ℝ)*simpleKernelConstant*(1+|Real.log (ζ*ε)|))*B.lengthC^((n+1)-2)))) := by
  obtain ⟨ζ,rK,hζ,hrK,hfloor⟩ := signed_original_kernel_density_bound d hcsmall
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
  intro ε hε hεr shift n R a D hR hRr ha hD hsmall₁ hsmall₂ P
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
  have hnon (u : AngularSpace n) (hu : u ∈ box) :
      signedRegularKernel (Complex.exp (Complex.I*(shift:ℂ))) (radialParameter d.theta ε)
        (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) ≠ 0 :=
    (hfloor ε hε (hεr.trans hs.1.le) shift n u
      (fun i => (abs_le.mpr ⟨hu.1 i,hu.2 i⟩).trans (hRr.trans hs.1.le))).1
  have hα1 : d.c₀*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hεr.trans hs.2.2.2.2.2.1.le) d.c₀_pos.le
    rwa [mul_inv_cancel₀ d.c₀_pos.ne'] at hh
  have hβ1 : ζ*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hεr.trans hs.2.2.2.2.2.2.le) hζ.le
    rwa [mul_inv_cancel₀ hζ.ne'] at hh
  have hK := signed_positive_diameter_integral (N := n+1) B ε a D R (d.c₀*ε) (ζ*ε) shift (-shift) P
    hε (hεr.trans hs.2.2.2.1.le) ha hD hsmall₁ hsmall₂ hR (hRr.trans hs.2.2.1.le)
    (hRr.trans hs.2.2.2.2.1.le) (mul_pos d.c₀_pos hε) hα1 (mul_pos hζ hε) hβ1
  have hi : IntegrableOn (fun u => allBranchExteriorDiameter u^(P+1)*
      signedExteriorKernelDensity (Complex.exp (Complex.I*(shift:ℂ))) d ε u) S :=
    (((@allBranchExterior_diameter_continuous (n+1)).pow (P+1)).continuousOn.mul
      (signed_kernel_density_continuousOn _ d box hhp hnon)).integrableOn_compact isCompact_Icc |>.mono_set hsub
  have hp (u : AngularSpace n) (hu : u ∈ S) :
      allBranchExteriorDiameter u^(P+1)*signedExteriorKernelDensity (Complex.exp (Complex.I*(shift:ℂ))) d ε u ≤
        4*(allBranchExteriorDiameter u^(P+1)*signedPositiveKernel d ε (d.c₀*ε) (ζ*ε) shift (-shift) u) := by
    have hh := mul_le_mul_of_nonneg_left
      (hfloor ε hε (hεr.trans hs.1.le) shift n u
        (fun i => (abs_le.mpr ⟨(hsub hu).1 i,(hsub hu).2 i⟩).trans (hRr.trans hs.1.le))).2
      (pow_nonneg (allBranchExterior_diameter_nonneg u) (P+1))
    nlinarith
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ u in S, 4*(allBranchExteriorDiameter u^(P+1)*
        signedPositiveKernel d ε (d.c₀*ε) (ζ*ε) shift (-shift) u) :=
      setIntegral_mono_on hi (hK.1.const_mul 4) (allBranchExterior_positive_diameter_region_measurable R a D) hp
    _ = 4*(∫ u in S, allBranchExteriorDiameter u^(P+1)*
        signedPositiveKernel d ε (d.c₀*ε) (ζ*ε) shift (-shift) u) := integral_const_mul _ _
    _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using
      mul_le_mul_of_nonneg_left hK.2 (by norm_num : (0:ℝ) ≤ 4)

end
end IsingBulk.HT.Contour
