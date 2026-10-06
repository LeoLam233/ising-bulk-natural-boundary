import IsingBulk.Tail.AllBranchExteriorFarChartDerivative
import IsingBulk.Tail.AllBranchExteriorFarScaleMajorant
import IsingBulk.Tail.AllBranchExteriorScaleGeometry

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem allBranchExterior_far_chart_window {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : ℝ, 0 < h → h ≤ r → 2*h ≤ 1 →
      h ≤ d.thetaB/2 → h ≤ (Real.pi-d.thetaB)/2 → ∀ η δ : ℝ, ∀ hδ : 0 < δ,
      ∀ Aμ cμ β : ℝ, 0 ≤ Aμ → 0 < cμ → cμ ≤ 1 → 0 ≤ β →
      ∃ S : ℕ → ℝ, Summable S ∧ (∀ N, 0 ≤ S N) ∧
      ∀ Dwin : ℝ, 0 ≤ Dwin → ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, 1 ≤ n →
        (n+1:ℝ) ≤ Dwin*Real.sqrt H →
        (∑ v : Fin (n+1), ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d (Real.exp (-H))
          (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h
            (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ v))
          (radialParameter d.theta (Real.exp (-H)))‖) ≤ S (n+1)*(H+1)^2 := by
  obtain ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,hbound⟩ :=
    allBranchExterior_far_chart_derivative B hcsmall j
  refine ⟨r,hr,?_⟩
  intro h hh hhr hh1 hhθ hhπ η δ hδ Aμ cμ β hAμ hcμ hcμ1 hβ
  obtain ⟨C₀,C₁,K,hC₀,hC₁,hK,hder⟩ := hbound h hh hhr hh1 hhθ hhπ η δ hδ
  obtain ⟨κ,hκ,hkernel⟩ := allBranchExterior_near_kernel_cost_radial_scalar B ζ cN CN hζ hcN hCN.le
  let M := allBranchExteriorFarScaleMajorant j G C D c A C₀ C₁ K Aμ cμ (max 1 B.lengthC) κ β
  have hsum := allBranchExterior_far_scale_majorant_summable j G C D c A C₀ C₁ K Aμ cμ (max 1 B.lengthC) κ β hA
  refine ⟨fun N => ‖M N‖,hsum.norm,fun N => norm_nonneg _,?_⟩
  intro Dwin hDwin
  let Ke := 1+2*|B.original.separationThreshold|+4*|B.original.C₀|
  have hKe : 0 < Ke := by dsimp [Ke]; positivity
  filter_upwards [eventually_ge_atTop (0:ℝ),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hr),
    allBranchExterior_window_epsilon_multiple Dwin Aμ cμ Ke hDwin hAμ hcμ hKe] with H hH hεr he
  intro n hn hwindow
  let N := n+1
  let b := allBranchMicroRadius Aμ cμ N
  let ρ := allBranchEqualityRadius β N
  let σ := ρ/Real.sqrt (N:ℝ)
  let W := allBranchExteriorFarChartJetCost j N C₀ C₁ K b ρ
  let L := allBranchExteriorFarLocalCost j N G C D c A W σ
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hb : 0 < b := microcoreRadius_pos Aμ cμ hcμ N hN
  have hb1 : b ≤ 1 := (microcoreRadius_le_prefactor Aμ cμ hAμ hcμ.le N hN).trans hcμ1
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ ≤ 1 := Real.exp_le_one_iff.mpr (by
    nlinarith [mul_nonneg hβ (Nat.cast_nonneg N (α := ℝ))])
  have hσ : 0 < σ := div_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hε := Real.exp_pos (-H)
  have heN : Ke*Real.exp (-H) ≤ b := by
    apply he N hN
    simpa only [N,Nat.cast_add,Nat.cast_one] using hwindow
  have hs₁ : B.original.separationThreshold*Real.exp (-H) ≤ b/2 := by
    have hcoeff : 2*B.original.separationThreshold ≤ Ke := by
      dsimp [Ke]
      linarith [le_abs_self B.original.separationThreshold,abs_nonneg B.original.C₀]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hε.le]
  have hs₂ : 2*B.original.C₀*Real.exp (-H) ≤ b/2 := by
    have hcoeff : 4*B.original.C₀ ≤ Ke := by
      dsimp [Ke]
      linarith [le_abs_self B.original.C₀,abs_nonneg B.original.separationThreshold]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hε.le]
  have hL : 0 ≤ L := by
    dsimp [L,W,allBranchExteriorFarLocalCost,allBranchExteriorFarNumeratorCost,allBranchExteriorFarChartJetCost]
    positivity
  let T := L*(σ⁻¹*(κ*(N:ℝ)^4*(max 1 B.lengthC)^N*(b/2)⁻¹))*(H+1)^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hkb := hkernel h (b/2) (2*h) H hh.le (by linarith) (by positivity) (by linarith)
    (by positivity) hh1 hH N 1 hN le_rfl
  simp only [Nat.sub_self,pow_zero,mul_one] at hkb
  have h_each (v : Fin (n+1)) :
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d (Real.exp (-H))
        (allBranchExteriorFarChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v))
        (radialParameter d.theta (Real.exp (-H)))‖ ≤ ((N.choose 2:ℕ):ℝ)*T := by
    have hd := hder (Real.exp (-H)) hε hεr.le n hn v b ρ hb hb1 hρ hρ1 hs₁ hs₂
    apply hd.trans
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hkb (inv_nonneg.mpr hσ.le)) hL) (Nat.cast_nonneg (N.choose 2))
    simpa only [T,L,W,σ,N,Nat.cast_add,Nat.cast_one,mul_assoc] using hh
  have hsumN := Finset.sum_le_sum (s := Finset.univ) (fun v _ => h_each v)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsumN
  have hchoose : (N.choose 2:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow N 2
  have hcount : (N:ℝ)*(N.choose 2:ℝ)*T ≤ (N:ℝ)^3*T := by
    apply mul_le_mul_of_nonneg_right _ hT
    have hh := mul_le_mul_of_nonneg_left hchoose (Nat.cast_nonneg N (α := ℝ))
    nlinarith
  have hfull : (N:ℝ)^3*T=M N*(H+1)^2 := by
    dsimp [T,M,allBranchExteriorFarScaleMajorant,L,W,σ,b,ρ]
    ring
  apply hsumN.trans
  change (N:ℝ)*((N.choose 2:ℝ)*T) ≤ ‖M N‖*(H+1)^2
  rw [← mul_assoc]
  exact (hcount.trans_eq hfull).trans (mul_le_mul_of_nonneg_right (le_abs_self (M N)) (sq_nonneg (H+1)))

end
end IsingBulk.Tail
