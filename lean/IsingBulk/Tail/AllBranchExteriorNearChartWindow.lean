import IsingBulk.Tail.AllBranchExteriorNearChartDerivative
import IsingBulk.Tail.AllBranchExteriorNearScaleMajorant
import IsingBulk.Tail.AllBranchExteriorScaleGeometry

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem allBranchExterior_near_chart_window {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2) (j : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : ℝ, 0 < h → h ≤ r → h ≤ 1 →
      h ≤ d.thetaB/2 → h ≤ (Real.pi-d.thetaB)/2 → ∀ η δ : ℝ, ∀ hδ : 0 < δ,
      ∀ Aμ cμ : ℝ, 0 ≤ Aμ → 0 < cμ → cμ ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∃ S : ℕ → ℝ, Summable S ∧ (∀ N, 0 ≤ S N) ∧
      ∀ Dwin : ℝ, 0 ≤ Dwin → ∀ᶠ H : ℝ in atTop, ∀ n : ℕ,
        (n+1:ℝ) ≤ Dwin*Real.sqrt H → 2*j+1 ≤ (n+1)*n →
        (∑ v : Fin (n+1), ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d (Real.exp (-H))
          (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h
            (allBranchMicroRadius Aμ cμ (n+1)) (allBranchEqualityRadius β (n+1)) hδ v))
          (radialParameter d.theta (Real.exp (-H)))‖) ≤ S (n+1)*(H+1)^2 := by
  obtain ⟨G,C,hG,hC,D,c,A,ζ,cN,CN,r,hD,hc,hA,hζ,hcN,hCN,hr,hbound⟩ :=
    allBranchExterior_near_chart_derivative B hcsmall j
  refine ⟨r,hr,?_⟩
  intro h hh hhr hh1 hhθ hhπ η δ hδ Aμ cμ hAμ hcμ hcμ1
  obtain ⟨C₀,C₁,K,hC₀,hC₁,hK,hder⟩ := hbound h hh hhr hhθ hhπ η δ hδ
  obtain ⟨κ,hκ,hkernel⟩ := allBranchExterior_near_kernel_cost_radial_scalar B ζ cN CN hζ hcN hCN.le
  obtain ⟨βs,hβs,hsum⟩ := allBranchExterior_near_scale_majorant_summable j G C D c A C₀ C₁ K Aμ cμ
    B.magnitudeUpper (max 1 B.lengthC) κ
  obtain ⟨βg,hβg,hgeometry⟩ := allBranchExterior_scale_geometry Aμ cμ B.magnitudeUpper hAμ hcμ hcμ1 B.magnitudeUpper_pos.le
  refine ⟨max βs βg,lt_of_lt_of_le hβs (le_max_left _ _),?_⟩
  intro β hβ
  let M := allBranchExteriorNearScaleMajorant j G C D c A C₀ C₁ K Aμ cμ B.magnitudeUpper (max 1 B.lengthC) κ β
  refine ⟨fun N => ‖M N‖,(hsum β ((le_max_left _ _).trans hβ)).norm,fun N => norm_nonneg _,?_⟩
  intro Dwin hDwin
  let Ke := 1+4*|B.original.separationThreshold|+8*|B.original.C₀|
  have hKe : 0 < Ke := by dsimp [Ke]; positivity
  filter_upwards [eventually_ge_atTop (0:ℝ),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hr),
    allBranchExterior_window_epsilon_multiple Dwin Aμ cμ Ke hDwin hAμ hcμ hKe] with H hH hεr he
  intro n hwindow horder
  let N := n+1
  let b := allBranchMicroRadius Aμ cμ N
  let ρ := allBranchEqualityRadius β N
  let V := (1+2*B.magnitudeUpper)/b
  let W := allBranchExteriorNearChartJetCost j N C₀ C₁ K b
  let L := allBranchExteriorNearLocalCost j N G C D c A W V
  have hgeo := hgeometry β ((le_max_right _ _).trans hβ) N (by dsimp [N]; omega)
  obtain ⟨hb,hb1,hρ,hρ1,hscale,hV,hVmag,hVρ⟩ := hgeo
  have hε := Real.exp_pos (-H)
  have heN : Ke*Real.exp (-H) ≤ b := by
    apply he N (by dsimp [N]; omega)
    simpa only [N,Nat.cast_add,Nat.cast_one] using hwindow
  have hs₁ : B.original.separationThreshold*Real.exp (-H) ≤ b/4 := by
    have hcoeff : 4*B.original.separationThreshold ≤ Ke := by
      dsimp [Ke]
      linarith [le_abs_self B.original.separationThreshold,abs_nonneg B.original.C₀]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hε.le]
  have hs₂ : 2*B.original.C₀*Real.exp (-H) ≤ b/4 := by
    have hcoeff : 8*B.original.C₀ ≤ Ke := by
      dsimp [Ke]
      linarith [le_abs_self B.original.C₀,abs_nonneg B.original.separationThreshold]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hε.le]
  have hL : 0 ≤ L := by
    dsimp [L,W,V,allBranchExteriorNearLocalCost,allBranchExteriorNearNumeratorCost,allBranchExteriorNearChartJetCost]
    positivity
  let Q := (n+1)*n-2*j
  let T := L*(κ*(N:ℝ)^4*(max 1 B.lengthC)^N*(b/4)⁻¹*(4*ρ)^(Q-1))*(H+1)^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hkb := hkernel h (b/4) (4*ρ) H hh.le hh1 (by positivity) (by linarith) (by positivity) hρ1 hH
    N Q (by dsimp [N]; omega) (by dsimp [Q]; omega)
  have h_each (v : Fin (n+1)) :
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d (Real.exp (-H))
        (allBranchExteriorNearChartWeight (n+1) d.thetaB η d.alpha δ h b ρ hδ v))
        (radialParameter d.theta (Real.exp (-H)))‖ ≤ ((N.choose 2:ℕ):ℝ)*T := by
    have hd := hder (Real.exp (-H)) hε hεr.le n horder v b ρ V hb hb1 hρ hρ1 hscale hV hVmag hVρ hs₁ hs₂
    apply hd.trans
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkb hL) (Nat.cast_nonneg (N.choose 2))
    exact hh.trans_eq (by dsimp [T,L,W,V,N,Q]; ring)
  have hsumN := Finset.sum_le_sum (s := Finset.univ) (fun v _ => h_each v)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsumN
  have hchoose : (N.choose 2:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow N 2
  have hcount : (N:ℝ)*(N.choose 2:ℝ)*T ≤ (N:ℝ)^3*T := by
    apply mul_le_mul_of_nonneg_right _ hT
    have hh := mul_le_mul_of_nonneg_left hchoose (Nat.cast_nonneg N (α := ℝ))
    nlinarith
  have hfull : (N:ℝ)^3*T=M N*(H+1)^2 := by
    have hpower : Q-1=N*(N-1)-(2*j+1) := by dsimp [Q,N]; omega
    dsimp [T]
    rw [hpower]
    dsimp [M,allBranchExteriorNearScaleMajorant,L,W,V,b,ρ]
    ring
  apply hsumN.trans
  change (N:ℝ)*((N.choose 2:ℝ)*T) ≤ ‖M N‖*(H+1)^2
  rw [← mul_assoc]
  exact (hcount.trans_eq hfull).trans (mul_le_mul_of_nonneg_right (le_abs_self (M N)) (sq_nonneg (H+1)))

end
end IsingBulk.Tail
