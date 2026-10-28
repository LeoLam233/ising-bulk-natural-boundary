import IsingBulk.HT22.Far.ActualSum
import IsingBulk.HT22.Near.ActualSum
import IsingBulk.HT22.Tail.PhysicalSupport
import IsingBulk.HT22.Geometry.SignedShellAggregation

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem le_near_far_masks (x δ : ℝ) (F : ℝ≥0∞) :
    F≤(if x≤δ then F else 0)+(if δ≤x then F else 0) := by
  by_cases h : x≤δ
  · simp [h]
  · have h' : δ≤x := le_of_lt (lt_of_not_ge h)
    simp [h,h']

theorem shell_sum_le_near_add_far {L I : Type*} [Fintype L] [Fintype I]
    (scale : ℕ → L → ℝ) (δ : ℝ) (f : ℕ → L → I → I → ℝ≥0∞) :
    (∑' q,∑ l,∑ i,∑ k,f q l i k)≤
      (∑' q,∑ l,∑ i,∑ k,if scale q l≤δ then f q l i k else 0)+
      (∑' q,∑ l,∑ i,∑ k,if δ≤scale q l then f q l i k else 0) := by
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro q
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum (fun k _ => le_near_far_masks (scale q l) δ (f q l i k))

/-- The exact actual signed right-region integral splits into the two
source shell budgets. Equality of the scale to the threshold may be counted
twice, which is harmless for this nonnegative upper bound. -/
theorem right_region_le_near_far_shells (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (a η δ τ ε δ₀ : ℝ) (hδ : δ<B.delta) (ha : |a|≤Real.pi)
    (rcut : ℝ → ℝ) (j m : ℕ) :
    (∫⁻ (x : Fin (m+2) → ℝ) in signedRightRegion a b B δ,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖)≤
    (∑' q, ∑ l : {l : ℤ // l∈preferredMeanIndices (m+3)},∑ i : Fin (m+3),∑ k : Fin (m+3),
      if shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
          (preferredDyadicRadius q) ε≤δ₀ then
        physicalShellMass a η b B δ τ ε (preferredDyadicRadius q) rcut j l.1 i k else 0)+
    (∑' q, ∑ l : {l : ℤ // l∈preferredMeanIndices (m+3)},∑ i : Fin (m+3),∑ k : Fin (m+3),
      if δ₀≤shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
          (preferredDyadicRadius q) ε then
        physicalShellMass a η b B δ τ ε (preferredDyadicRadius q) rcut j l.1 i k else 0) := by
  apply (signedRightRegion_lintegral_le_shells (show 0<m+2 by omega) a b B hδ ha
    (fun x : Fin (m+2) → ℝ => ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖)).trans
  exact shell_sum_le_near_add_far (L := {l : ℤ // l∈preferredMeanIndices (m+3)}) (I := Fin (m+3))
    (fun q l => shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
      (preferredDyadicRadius q) ε) δ₀
    (fun q l i k => physicalShellMass a η b B δ τ ε (preferredDyadicRadius q) rcut j l.1 i k)


/-- Complete actual right-region tail mass, combining the new quadratic
near suppression with the superexponential far estimate. -/
theorem actual_right_region_mass (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ H A : ℝ, ∃ L : ℕ, 0<H ∧ 0<A ∧
    ∀ a η : ℝ, |a|≤Real.pi → ∀ n : ℕ, 2*j+3<(2*n+3)^2 → ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ δ : ℝ, δ≤δB →
    (∫⁻ (x : Fin (2*n+2) → ℝ) in signedRightRegion a b B δ,
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖)≤
      ENNReal.ofReal ((H*nearOrderEnvelope (2*n+3)+farOrderEnvelope A L (2*n+3))*(1+|Real.log ε|)) := by
  obtain ⟨capN,hcapN,hcapNa,hnear⟩ := Near.actual_near_shell_sum b
  obtain ⟨capF,hcapF,hcapFa,hfar⟩ := actual_far_shell_sum b
  refine ⟨min capN capF,lt_min hcapN hcapF,(min_le_left _ _).trans_lt hcapNa,?_⟩
  intro B hB
  obtain ⟨eN,tN,dN,heN,htN,hdN,hdNB,hnear⟩ := hnear B (hB.trans_le (min_le_left _ _))
  obtain ⟨eF,tF,dF,heF,htF,hdF,hdFB,hfar⟩ := hfar B (hB.trans_le (min_le_right _ _))
  let d := min dN dF
  refine ⟨min eN eF,min tN tF,d,lt_min heN heF,lt_min htN htF,lt_min hdN hdF,
    (min_le_left _ _).trans_lt hdNB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨δ₀,H,hδ₀,_hδ₀1,hH,hnear⟩ := hnear rcut hrcut hrper j
  obtain ⟨A,L,hA,hfar⟩ := hfar δ₀ hδ₀ rcut hrcut hrper j
  refine ⟨H,A,L,hH,hA,?_⟩
  intro a η ha n hdeg ε τ hε hεr hτ hτr δ hδ
  have hδN : δ≤dN := hδ.trans (min_le_left _ _)
  have hδF : δ≤dF := hδ.trans (min_le_right _ _)
  have hn := hnear a η n hdeg ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) δ hδN
  have hf := hfar a η (2*n) ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) δ hδF
  have hsplit := right_region_le_near_far_shells b B a η δ τ ε δ₀
    (hδN.trans_lt hdNB) ha rcut j (2*n)
  apply hsplit.trans
  have hh := add_le_add hn hf
  have hn0 : 0≤H*nearOrderEnvelope (2*n+3)*(1+|Real.log ε|) :=
    mul_nonneg (mul_nonneg hH.le (nearOrderEnvelope_nonneg _)) (by positivity)
  have hf0 : 0≤farOrderEnvelope A L (2*n+3)*(1+|Real.log ε|) :=
    mul_nonneg (farOrderEnvelope_nonneg hA.le _ _) (by positivity)
  rw [←ENNReal.ofReal_add hn0 hf0,←add_mul] at hh
  simpa only [Near.dyadicScale,Near.physicalShellMass,physicalShellMass] using hh

theorem actual_whole_angular_mass (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ H A : ℝ, ∃ L : ℕ, 0<H ∧ 0<A ∧
    ∀ a η : ℝ, |a|≤Real.pi → ∀ n : ℕ, 2*j+3<(2*n+3)^2 → ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ δ : ℝ, δ≤δB → PreferredRightCutoffData b B δ rcut →
    (∫⁻ (x : Fin (2*n+2) → ℝ) in angularBox (2*n+2),
      ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
        preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖)≤
      ENNReal.ofReal ((H*nearOrderEnvelope (2*n+3)+farOrderEnvelope A L (2*n+3))*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_right_region_mass b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨H,A,L,hH,hA,hsource⟩ := hsource rcut hrcut hrper j
  refine ⟨H,A,L,hH,hA,?_⟩
  intro a η ha n hdeg ε τ hε hεr hτ hτr δ hδ hcut
  rw [transportedNorm_lintegral_eq_signedRightRegion _ a b B τ rcut hcut j
    (IsingBulk.Branch.radialParameter b.alpha ε)]
  exact hsource a η ha n hdeg ε τ hε hεr hτ hτr δ hδ

end
end IsingBulk.HT22.Far
