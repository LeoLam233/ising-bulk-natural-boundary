import IsingBulk.Tail.SectorMicrocoreAngleBox
import IsingBulk.HT.Tail.NegativeSectorMicrocoreBridge
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.SelectorDerivativeDistribution

/-! Exact angleBox-to-local-chart microcore identification, including the
original pulled-density normalization and lower-branch period shift. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.First IsingBulk.Branch MeasureTheory Set Filter
open scoped BigOperators Topology

def negativeAngleBoxMicrocoreIntegral (n : ℕ) (d : LocalBranchData) (eta delta : ℝ) (hd : 0 < delta)
    (eps a : ℝ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox (n+2),
    ((scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi)*
      angularSelector (constructedSelector d.thetaB eta d.alpha) theta *
        ∏ i, sectorBranch d.thetaB delta hd (theta i)):ℝ)*
      negativePulledDensity (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps)) d.tau 0 s theta

theorem negative_angleBoxMicrocoreIntegral_eq (n : ℕ) (d : LocalBranchData) (eta delta eps a : ℝ)
    (hd : 0 < delta) (hds : delta ≤ 1/2) (heps : 0 < eps) (ha : 0 < a)
    (had : a ≤ delta/2) (hab : a ≤ d.thetaB/2) (hapi : a ≤ (Real.pi-d.thetaB)/2)
    (s : ℂ) (_hs : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps) < (sourceS s).im) :
    negativeAngleBoxMicrocoreIntegral n d eta delta hd eps a s = negativeSectorMicrocoreIntegral n d eta delta hd eps a s := by
  let r := Real.exp (-d.c₀*eps)
  let center : Fin (n+2) → ℝ := fun _ => 2*Real.pi-d.thetaB
  let F : (Fin (n+2) → ℝ) → ℂ := fun theta =>
    (scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi):ℝ)*negativeSourceAngularDensity r s theta
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have := d.c₀_pos
    nlinarith
  have hweight (theta : Fin (n+2) → ℝ) :
      scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi)*
      angularSelector (constructedSelector d.thetaB eta d.alpha) theta *
      (∏ i, sectorBranch d.thetaB delta hd (theta i)) =
        scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi) := by
    let u := fun i => theta i+d.thetaB-2*Real.pi
    have he : theta = fun i => (u i-d.thetaB)+2*Real.pi := by funext i; dsimp [u]; ring
    have hh := sector_microcore_weight_identity d.thetaB delta d.alpha eta a d.thetaB_pos d.thetaB_lt
      hd hds d.alpha_pos ha had hab hapi u
    change scaledMicroCutoff (n+2) a u * angularSelector (constructedSelector d.thetaB eta d.alpha) theta *
      (∏ i, sectorBranch d.thetaB delta hd (theta i)) = _
    rw [he,constructedSelector_all_period,sectorBranch_all_period]
    simp only [sectorAssignmentWeight,sectorLabel] at hh
    norm_num only [show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide,ite_false] at hh
    simpa only [show (fun i => u i-d.thetaB+2*Real.pi+d.thetaB-2*Real.pi)=u by funext i; ring] using hh
  have hnorm (theta : Fin (n+2) → ℝ) :
      negativePulledDensity (constructedSelector d.thetaB eta d.alpha) r d.tau 0 s theta =
        ((n+2).factorial:ℂ)⁻¹*negativeSourceAngularDensity r s theta := by
    simpa only [negativeSourceAngularDensity,signedSourceAngularDensity,mul_assoc] using
      signedPulledDensity_original (-1) (constructedSelector d.thetaB eta d.alpha) r d.tau s theta
  have hsupport : ∀ theta, theta ∉ angleBox (n+2) → F theta=0 := by
    intro theta hout
    by_cases hz : scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi)=0
    · simp [F,hz]
    · have hu := scaledMicroCutoff_jet_tsupport ha [] (subset_closure hz)
      exfalso
      apply hout
      constructor <;> intro i
      · have hh := (abs_le.mp (hu i)).1
        have hb := d.thetaB_lt
        have hpi := Real.pi_pos
        linarith
      · have hh := (abs_le.mp (hu i)).2
        have hb := d.thetaB_pos
        linarith
  rw [negative_sectorMicrocoreIntegral_eq n d eta delta eps a hd hds ha had hab hapi]
  unfold negativeAngleBoxMicrocoreIntegral negativeOriginalMicrocoreIntegral
  change (∫ theta in angleBox (n+2), (_:ℂ)*negativePulledDensity _ r d.tau 0 s theta) = _
  simp_rw [hweight,hnorm]
  rw [show (fun theta : Fin (n+2) → ℝ =>
      (scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi):ℝ)*
        (((n+2).factorial:ℂ)⁻¹*negativeSourceAngularDensity r s theta)) =
      (fun theta => ((n+2).factorial:ℂ)⁻¹*F theta) by funext theta; dsimp [F]; ring,
    integral_const_mul,setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  congr 1
  rw [← integral_add_right_eq_self F center]
  apply integral_congr_ae
  filter_upwards [] with u
  have hcoord : (fun i => (u+center) i+d.thetaB-2*Real.pi)=u := by funext i; dsimp [center]; ring
  have hperiod : u+center = fun i => (u i-d.thetaB)+2*Real.pi := by funext i; dsimp [center]; ring
  dsimp only [F]
  rw [hcoord,hperiod,negativeSourceAngularDensity_all_period]


theorem negative_angleBoxMicrocoreIntegral_iteratedDeriv_eq (n : ℕ) (d : LocalBranchData)
    (eta delta eps a : ℝ) (hd : 0 < delta) (hds : delta ≤ 1/2) (heps : 0 < eps) (ha : 0 < a)
    (had : a ≤ delta/2) (hab : a ≤ d.thetaB/2) (hapi : a ≤ (Real.pi-d.thetaB)/2)
    (s : ℂ) (hs : s ∈ dampingDomain (Real.exp (-d.c₀*eps))) (j : ℕ) :
    iteratedDeriv j (negativeAngleBoxMicrocoreIntegral n d eta delta hd eps a) s =
      iteratedDeriv j (negativeSectorMicrocoreIntegral n d eta delta hd eps a) s := by
  have he : negativeAngleBoxMicrocoreIntegral n d eta delta hd eps a =ᶠ[𝓝 s]
      negativeSectorMicrocoreIntegral n d eta delta hd eps a := by
    filter_upwards [(dampingDomain_isOpen _).mem_nhds hs] with z hz
    exact negative_angleBoxMicrocoreIntegral_eq n d eta delta eps a hd hds heps ha had hab hapi z hz.2
  exact he.iteratedDeriv_eq j

end
end IsingBulk.HT.Tail
