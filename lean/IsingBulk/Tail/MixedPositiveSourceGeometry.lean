import IsingBulk.Tail.MixedAngularCells
import IsingBulk.Tail.MixedSourceGeometry
import IsingBulk.Tail.MixedBranchCone
import IsingBulk.Tail.MixedVolumeMajorant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixed_lower_angular_profile (b x : ℝ) :
    |sectorDisplacement b x|≤|x+b-2*Real.pi| := by
  have hh := Real.abs_cos_sub_cos_le x (2*Real.pi-b)
  rw [Real.cos_two_pi_sub,show x-(2*Real.pi-b)=x+b-2*Real.pi by ring] at hh
  simpa only [sectorDisplacement,abs_sub_comm] using hh

theorem mixed_lower_angular_plateau {b η α R x : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4) (hα : 0<α)
    (hR : 0≤R) (hRη : R≤η/2) (hx : |x+b-2*Real.pi|≤R) :
    (constructedSelector b η α).p =ᶠ[𝓝 x] (fun _ => 0) ∧
    (constructedSelector b η α).m =ᶠ[𝓝 x] (fun _ => 1) := by
  apply constructed_branch_plateau_germ hb hη hηsmall hα
  have hs := pow_le_pow_left₀ (abs_nonneg _) hx 2
  rw [sq_abs] at hs
  nlinarith [lowerChord_le_coordinate_square b x]

/-- Source geometry on the enlarged positive angular cells is proved
uniformly in the spectators and their coupled occupancy. -/
theorem mixed_positive_source_geometry (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α outer : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (ho : 0<outer) :
    ∃ R e t₀ : ℝ,0<R ∧ 0<e ∧ 0<t₀ ∧ R≤η/2 ∧
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N),
      1≤N → 0<eps → eps<e → 0≤τ → τ<t₀ → 0≤lam → lam≤1 →
      0≤θ j+d.thetaB-2*Real.pi → θ j+d.thetaB-2*Real.pi≤R →
      outer/2≤|sectorDisplacement d.thetaB (θ q)| →
      let f := constructedSelector d.thetaB η α
      let s := radialParameter d.theta eps
      let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
      (∀ i,0<(sourceW s (y i)).im) ∧
      mixedSourceSlope s (y j)≠0 ∧
      (2/3:ℝ)*‖mixedSourceSlope s (y j)‖≤(mixedSourceSlope s (y j)).re ∧
      ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 := by
  obtain ⟨iS,cS,eS,tS,hiS,_hiSo,hcS,heS,htS,hSlope⟩ :=
    mixed_actual_profile_slope_separation d hcsmall outer ho
  obtain ⟨cG,eG,tG,hcG,heG,htG,hSource⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  obtain ⟨rC,tC,hrC,htC,hCone⟩ := mixed_actual_positive_branch_cone d
  let R := min (rC/2) (min iS (η/2))
  have hR : 0<R := lt_min (half_pos hrC) (lt_min hiS (half_pos hη))
  have hRC : R<rC := (min_le_left _ _).trans_lt (half_lt_self hrC)
  have hRI : R≤ iS := (min_le_right _ _).trans (min_le_left _ _)
  have hRη : R≤η/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,min eS (min eG rC),min tS (min tG tC),hR,
    lt_min heS (lt_min heG hrC),lt_min htS (lt_min htG htC),hRη,?_⟩
  intro N eps τ lam θ j q hN he heSmall hτ hτSmall hl0 hl1 hu0 huR hq
  have hτS := hτSmall.trans_le (min_le_left _ _)
  have hτG := hτSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτC := hτSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hLamTau : lam*τ≤τ := mul_le_of_le_one_left hτ hl1
  have hu : |θ j+d.thetaB-2*Real.pi|≤R := by rwa [abs_of_nonneg hu0]
  have hs := hSource η α hη hηsmall hα N eps τ lam θ (radialParameter d.theta eps)
    hN he (heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hl0 hl1
    (hLamTau.trans_lt hτG) (by simp; positivity)
  have hW (i : Fin N) : 0<(sourceW (radialParameter d.theta eps)
      (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i)).im := by
    obtain ⟨v,_hv,_hy,_hd,hw⟩ := hs.2 i
    exact hw
  have hSep := hSlope η α hη hηsmall hα N eps τ lam θ j q (radialParameter d.theta eps)
    hN he (heSmall.trans_le (min_le_left _ _)) hτ hl0 hl1 (hLamTau.trans_lt hτS)
    ((mixed_lower_angular_profile d.thetaB (θ j)).trans (hu.trans hRI)) hq (by simp; positivity)
  obtain ⟨hp,hm⟩ := mixed_lower_angular_plateau d.a_pos hη hηsmall hα hR.le hRη hu
  have hCo := hCone N eps τ lam _ θ j (by omega) he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ hτC hl0 hl1
    (fun x => thresholdStep_range _ _ _) hp.eq_of_nhds hm.eq_of_nhds hu0 (huR.trans_lt hRC)
  exact ⟨hW,hSep.1,hCo,hSep.2.1⟩

end
end IsingBulk.Tail
