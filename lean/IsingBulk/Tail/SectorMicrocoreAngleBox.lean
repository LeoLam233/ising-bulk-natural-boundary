import IsingBulk.Tail.SectorMicrocoreBridge
import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.SelectorDerivativeDistribution

/-! Exact angleBox-to-local-chart microcore identification, including the
original pulled-density normalization and lower-branch period shift. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set Filter
open scoped BigOperators Topology

theorem sourceReducedAngularDensity_all_period {N : ℕ} (r : ℝ) (s : ℂ)
    (theta : Fin N → ℝ) :
    sourceReducedAngularDensity r s (fun i => theta i+2*Real.pi)=sourceReducedAngularDensity r s theta := by
  have hy : angleTuple r (fun i => theta i+2*Real.pi)=angleTuple r theta := by
    funext i; exact anglePoint_add_period r (theta i)
  have hz : (fun i => globalRoot s (anglePoint r (theta i+2*Real.pi))) =
      (fun i => globalRoot s (anglePoint r (theta i))) := by
    funext i; rw [anglePoint_add_period]
  simp only [sourceReducedAngularDensity,angleProductJacobian,angleJacobian,anglePoint_add_period,hy]

theorem constructedSelector_all_period {N : ℕ} (b eta alpha : ℝ) (theta : Fin N → ℝ) :
    angularSelector (constructedSelector b eta alpha) (fun i => theta i+2*Real.pi)=
      angularSelector (constructedSelector b eta alpha) theta := by
  simp only [angularSelector,selectorWeight,constructedSelector,periodicUpperA,Real.sin_add_two_pi]

theorem sectorBranch_all_period {N : ℕ} (b delta : ℝ) (hd : 0 < delta) (theta : Fin N → ℝ) :
    (∏ i, sectorBranch b delta hd (theta i+2*Real.pi)) = ∏ i, sectorBranch b delta hd (theta i) := by
  simp only [sectorBranch,sectorDisplacement,Real.cos_add_two_pi]

def angleBoxMicrocoreIntegral (n : ℕ) (d : LocalBranchData) (eta delta : ℝ) (hd : 0 < delta)
    (eps a : ℝ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox (n+2),
    ((scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi)*
      angularSelector (constructedSelector d.thetaB eta d.alpha) theta *
        ∏ i, sectorBranch d.thetaB delta hd (theta i)):ℝ)*
      pulledDensity (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps)) d.tau 0 s theta

theorem angleBoxMicrocoreIntegral_eq (n : ℕ) (d : LocalBranchData) (eta delta eps a : ℝ)
    (hd : 0 < delta) (hds : delta ≤ 1/2) (heps : 0 < eps) (ha : 0 < a)
    (had : a ≤ delta/2) (hab : a ≤ d.thetaB/2) (hapi : a ≤ (Real.pi-d.thetaB)/2)
    (s : ℂ) (hs : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps) < (sourceS s).im) :
    angleBoxMicrocoreIntegral n d eta delta hd eps a s = sectorMicrocoreIntegral n d eta delta hd eps a s := by
  let r := Real.exp (-d.c₀*eps)
  let center : Fin (n+2) → ℝ := fun _ => 2*Real.pi-d.thetaB
  let F : (Fin (n+2) → ℝ) → ℂ := fun theta =>
    (scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi):ℝ)*sourceReducedAngularDensity r s theta
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
      pulledDensity (constructedSelector d.thetaB eta d.alpha) r d.tau 0 s theta =
        ((n+2).factorial:ℂ)⁻¹*sourceReducedAngularDensity r s theta := by
    have hadm := (globalRoot_admissible hr hr1 hs).toTuple (n+2) (angleTuple r theta)
      (fun i => anglePoint_norm hr.le (theta i))
    simpa only [sourceReducedAngularDensity,mul_assoc] using
      pulledDensity_original (constructedSelector d.thetaB eta d.alpha) r d.tau s theta hadm
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
  rw [sectorMicrocoreIntegral_eq n d eta delta eps a hd hds ha had hab hapi]
  unfold angleBoxMicrocoreIntegral originalMicrocoreIntegral
  change (∫ theta in angleBox (n+2), (_:ℂ)*pulledDensity _ r d.tau 0 s theta) = _
  simp_rw [hweight,hnorm]
  rw [show (fun theta : Fin (n+2) → ℝ =>
      (scaledMicroCutoff (n+2) a (fun i => theta i+d.thetaB-2*Real.pi):ℝ)*
        (((n+2).factorial:ℂ)⁻¹*sourceReducedAngularDensity r s theta)) =
      (fun theta => ((n+2).factorial:ℂ)⁻¹*F theta) by funext theta; dsimp [F]; ring,
    integral_const_mul,setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  congr 1
  rw [← integral_add_right_eq_self F center]
  apply integral_congr_ae
  filter_upwards [] with u
  have hcoord : (fun i => (u+center) i+d.thetaB-2*Real.pi)=u := by funext i; dsimp [center]; ring
  have hperiod : u+center = fun i => (u i-d.thetaB)+2*Real.pi := by funext i; dsimp [center]; ring
  dsimp only [F]
  rw [hcoord,hperiod,sourceReducedAngularDensity_all_period]


theorem angleBoxMicrocoreIntegral_iteratedDeriv_eq (n : ℕ) (d : LocalBranchData)
    (eta delta eps a : ℝ) (hd : 0 < delta) (hds : delta ≤ 1/2) (heps : 0 < eps) (ha : 0 < a)
    (had : a ≤ delta/2) (hab : a ≤ d.thetaB/2) (hapi : a ≤ (Real.pi-d.thetaB)/2)
    (s : ℂ) (hs : s ∈ dampingDomain (Real.exp (-d.c₀*eps))) (j : ℕ) :
    iteratedDeriv j (angleBoxMicrocoreIntegral n d eta delta hd eps a) s =
      iteratedDeriv j (sectorMicrocoreIntegral n d eta delta hd eps a) s := by
  have he : angleBoxMicrocoreIntegral n d eta delta hd eps a =ᶠ[𝓝 s]
      sectorMicrocoreIntegral n d eta delta hd eps a := by
    filter_upwards [(dampingDomain_isOpen _).mem_nhds hs] with z hz
    exact angleBoxMicrocoreIntegral_eq n d eta delta eps a hd hds heps ha had hab hapi z hz.2
  exact he.iteratedDeriv_eq j

end
end IsingBulk.Tail
