import IsingBulk.HT22.FullTail.AbsoluteAssembly
import IsingBulk.HT22.FullTail.TransportAdapter
import IsingBulk.HT22.Tail.ActualIntegralIdentity
import IsingBulk.Preferred22.RightCutoff
namespace IsingBulk.HT22.FullTail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Physical IsingBulk.HT22.Selected
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def coefficientMass (negative : Bool) (p j : ℕ) (α ε : ℝ) (n : ℕ) : ℝ :=
  ‖iteratedDeriv j (signedCoefficient negative (2*(p/2+n)+3))
    (IsingBulk.Branch.radialParameter α ε)‖

/-- The complete actual signed odd coefficient tail, on one fixed constructed
contour and cutoff. All physical component bounds are proved, not premises. -/
theorem actual_absolute_tail (d : PreferredBranchData) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ p : ℕ,5≤p → Odd p → ∀ j : ℕ,
    j≤IsingBulk.HT.First.derivativeOrder p → ∃ C : ℝ,0<C ∧
    ∀ negative : Bool,∀ ε : ℝ,0<ε → ε<ε₀ →
    Summable (coefficientMass negative p j d.alpha ε) ∧
    (∑' n,coefficientMass negative p j d.alpha ε n)≤C*(1+|Real.log ε|) := by
  obtain ⟨cR,hcR,_,hR⟩ := Tail.actual_right_integral_identity d
  obtain ⟨cW,hcW,_,hW⟩ := Far.actual_high_odd_mass_sum d
  obtain ⟨cA,hcA,_,hA⟩ := Anchor.actual_anchor_absolute_majorant d
  let cap := min cR (min cW cA)
  have hcap : 0<cap := by dsimp [cap];positivity
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨eR,tR,dR,heR,htR,hdR,_,hR⟩ := hR B (hB.trans_le (by simp [cap]))
  obtain ⟨eW,tW,dW,heW,htW,hdW,_,hW⟩ := hW B (hB.trans_le (by simp [cap]))
  let δ := min dR (min dW (preferredRightMargin d B))/2
  have hδ : 0<δ := by dsimp [δ];positivity [ (preferredRightMargin_bounds d B).1 ]
  have hδR : δ≤dR := by dsimp [δ];linarith [min_le_left dR (min dW (preferredRightMargin d B))]
  have hδW : δ≤dW := by
    have h := (min_le_right dR (min dW (preferredRightMargin d B))).trans (min_le_left _ _)
    dsimp [δ];linarith
  have hδM : δ≤preferredRightMargin d B := by
    have h := (min_le_right dR (min dW (preferredRightMargin d B))).trans (min_le_right _ _)
    dsimp [δ];linarith [(preferredRightMargin_bounds d B).1]
  let r := preferredRightCutoff d δ
  have hcut : PreferredRightCutoffData d B δ r := preferred_right_cutoff_data_of_le d B hδ hδM
  obtain ⟨eA,tA,heA,htA,hA⟩ := hA B (hB.trans_le (by simp [cap])) δ hδ
  obtain ⟨ρ,hρ,_,hF⟩ := selected_absolute_upper_tail d hcap
  let τ := min tR (min tW (min tA ρ))/2
  have hτ : 0<τ := by dsimp [τ];positivity
  have hτR : τ<tR := by dsimp [τ];linarith [min_le_left tR (min tW (min tA ρ))]
  have hτW : τ<tW := by
    have h := (min_le_right tR (min tW (min tA ρ))).trans (min_le_left _ _)
    dsimp [τ];linarith
  have hτA : τ<tA := by
    have h := ((min_le_right tR (min tW (min tA ρ))).trans (min_le_right _ _)).trans (min_le_left _ _)
    dsimp [τ];linarith
  have hτρ : τ<ρ := by
    have h := ((min_le_right tR (min tW (min tA ρ))).trans (min_le_right _ _)).trans (min_le_right _ _)
    dsimp [τ];linarith
  let e := min eR (min eW (min eA ρ))
  have he : 0<e := by dsimp [e];positivity
  refine ⟨e,he,?_⟩
  intro p hp5 hp j hj
  obtain ⟨HF,hHF,hF⟩ := hF τ hτ hτρ j
  obtain ⟨CW,hCW,hW⟩ := hW r hcut.2.2.1 hcut.2.2.2.1 p hp5 hp j hj
  obtain ⟨CA,hCA,hAs,hA⟩ := hA r hcut j
  let MA := ∑' k,Anchor.oddAnchorEnvelope CA j k
  have hMA : 0≤MA := tsum_nonneg (fun k => by unfold Anchor.oddAnchorEnvelope shellOrderEnvelope;positivity)
  refine ⟨HF+2*(CW+MA)+1,by positivity,?_⟩
  intro negative ε hε hεe
  have heR' : ε<eR := hεe.trans_le (by simp [e])
  have heW' : ε<eW := hεe.trans_le (by simp [e])
  have heA' : ε<eA := hεe.trans_le (by simp [e])
  have heρ' : ε<ρ := hεe.trans_le (by simp [e])
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let F := fun n : ℕ => ‖iteratedDeriv j (selectedIntegral negative (2*(p/2+n+1)) τ B.p B.m) s‖
  let R := fun n : ℕ => ‖iteratedDeriv j (rightPopulationIntegral negative (2*(p/2+n+1)) τ preferredPopulationCutoff B.p B.m r) s‖
  let A := fun n : ℕ => Anchor.derivativeMass negative (p/2+n) τ B.p B.m r j s
  have hFs : Summable F ∧ (∑' n,F n)≤HF := by
    convert hF negative (p/2+1) (by omega) ε hε heρ' using 1 <;>
      simp only [F,s,B,Nat.add_comm,Nat.add_left_comm]
  have hRe (n : ℕ) : R n=‖Far.wholeTransportedIntegral d B r j
      (constraintAngle negative) (constraintAngle negative) (p/2+n) ε τ‖ := by
    have hdegree := full_shell_exponent hp (Far.high_odd_order_ge hp n) hj
    have hh := hR δ hδR r hcut j (p/2+n) (by omega) negative τ hτ.le hτR j le_rfl ε hε heR'
    dsimp only [R,s]
    rw [show 2*(p/2+n+1)=2*(p/2+n)+2 by omega,hh,transportedIntegral_eq_whole]
  have hRW := hW (constraintAngle negative) (constraintAngle negative)
    (Tail.constraintAngle_abs_le_pi negative) ε τ hε heW' hτ.le hτW δ hδW hcut
  have hRs : Summable R := hRW.2.1.congr (fun n => (hRe n).symm)
  have hRb : (∑' n,R n)≤CW*(1+|Real.log ε|) := by simpa only [hRe] using hRW.2.2
  have hAb (n : ℕ) : A n≤Anchor.oddAnchorEnvelope CA j (p/2+n) :=
    hA negative (p/2+n) ε τ hε heA' hτ.le hτA j le_rfl
  have hinj : Function.Injective (fun n : ℕ => p/2+n) := by intro n m h; change p/2+n=p/2+m at h; omega
  have hApart := hAs.comp_injective hinj
  have hAs' : Summable A := hApart.of_nonneg_of_le
    (fun n => Anchor.derivativeMass_nonneg negative _ τ B.p B.m r j s) hAb
  have hAb' : (∑' n,A n)≤MA := (hAs'.tsum_le_tsum hAb hApart).trans
    (tsum_comp_le_tsum_of_inj hAs (fun k => by unfold Anchor.oddAnchorEnvelope shellOrderEnvelope;positivity) hinj)
  have hcoeff (n : ℕ) : coefficientMass negative p j d.alpha ε n≤F n+2*(R n+A n) := by
    simpa only [coefficientMass,F,R,A,s,show 2*(p/2+n+1)+1=2*(p/2+n)+3 by omega]
      using signed_coefficient_norm_le negative (p/2+n) d B hτ.le hε r hcut.2.2.1 j
  obtain ⟨hsum,hbound⟩ := absolute_sum_of_components _ F R A
    (fun n => norm_nonneg _) hFs.1 hRs hAs' hcoeff hFs.2 hRb hAb'
  refine ⟨hsum,hbound.trans ?_⟩
  have hl : 0≤|Real.log ε| := abs_nonneg _
  nlinarith
end
end IsingBulk.HT22.FullTail
