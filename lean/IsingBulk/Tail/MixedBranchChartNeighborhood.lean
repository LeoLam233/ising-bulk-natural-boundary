import IsingBulk.Tail.MixedSourceGeometry
import IsingBulk.Tail.MicrocorePhaseMagnitude

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology

/-- A fixed scalar branch neighborhood is reached by shrinking the inner profile
before choosing any dimension or occupancy. -/
theorem mixed_actual_branch_chart_neighborhood (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (U : Set (ℂ × ℂ))
    (hU : IsOpen U) (hbase : (radialParameter d.theta 0,0)∈U)
    (cap : ℝ) (hcap : 0<cap) :
    ∃ inner c e t₀ : ℝ,0< inner ∧ inner≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      |sectorDisplacement d.thetaB (θ i)|≤ inner →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      (s,mixedSourcePhase s (deformedPoint (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ lam θ i))∈U := by
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU _ hbase
  let inner := min cap (min (1/400:ℝ) ((r/24)^2))
  have hi : 0< inner := lt_min hcap (lt_min (by norm_num) (sq_pos_of_pos (by positivity)))
  obtain ⟨cG,eG,tG,hcG,heG,htG,hG⟩ := mixed_actual_uniform_source_data d hcsmall inner hi
  let c := min cG 1
  let e := min eG (r/4)
  refine ⟨inner,c,e,tG,hi,min_le_left _ _,lt_min hcG zero_lt_one,
    lt_min heG (by positivity),htG,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ i s hN heps hepslt hτ hl0 hl1 htl hprofile hs
  have hsG := hs.trans (mul_le_mul_of_nonneg_right (min_le_left cG 1) heps.le)
  obtain ⟨_,hcoords⟩ := hG η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 htl hsG
  obtain ⟨v,_hv,_hy,hd,_hW⟩ := hcoords i
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i
  have hw : ‖1-sourceW s y‖≤2*inner := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (sourceW s y)
      (limitingAngularW d.thetaB (θ i):ℂ) 1
    rw [limitingAngularW_sub_one_norm] at hh
    rw [norm_sub_rev]
    exact hh.trans (by linarith)
  have his : inner≤1/400 := (min_le_right cap _).trans (min_le_left _ _)
  have hir : inner≤(r/24)^2 := (min_le_right cap _).trans (min_le_right _ _)
  have hphase := lowerArccos_norm_upper (sourceW s y) (hw.trans (by linarith))
  have hsqrt : Real.sqrt ‖1-sourceW s y‖<r/6 := by
    have hsq := Real.sq_sqrt (norm_nonneg (1-sourceW s y))
    nlinarith [Real.sqrt_nonneg ‖1-sourceW s y‖]
  have hp : ‖mixedSourcePhase s y‖<r := by
    change ‖lowerArccos (sourceW s y)‖<r
    nlinarith
  have hds : ‖s-radialParameter d.theta 0‖<r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub s (radialParameter d.theta eps) (radialParameter d.theta 0)
    rw [radialParameter_sub_zero_norm d.theta eps heps.le] at hh
    have hsc := hs.trans (mul_le_mul_of_nonneg_right (min_le_right cG 1) heps.le)
    have he := hepslt.trans_le (min_le_right eG (r/4))
    nlinarith
  apply hrU
  change dist (s,mixedSourcePhase s y) (radialParameter d.theta 0,0)<r
  rw [Prod.dist_eq]
  simpa only [dist_eq_norm,sub_zero] using max_lt hds hp

end
end IsingBulk.Tail
