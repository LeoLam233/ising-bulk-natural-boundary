import IsingBulk.Tail.SelectedFIndexedPairs
import IsingBulk.Tail.SelectedFDiskSupport

/-! Source-attached selected-F Schur pair bounds. The compact assignment is
geometric, and all compact perturbations are compared with actual radial
roots. True branch roots are kept at the disk point during comparison. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology BigOperators

 def selectedCompactIndexSet {N : ℕ} (b η : ℝ) (θ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => η^2/2 ≤ lowerChord b (θ i))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
 theorem selected_actual_pair_bounds (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C q : ℝ, 0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < q ∧ q < 1 ∧
        ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → θ ∈ angleBox N →
          θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ) →
          ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
          ∃ color : Fin N → Bool,
            (∀ i ∈ selectedCompactIndexSet d.thetaB η θ, ∀ j ∈ selectedCompactIndexSet d.thetaB η θ,
              color i=color j →
              ‖pairKernel
                (selectedContinuedRoot s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ i))
                (selectedContinuedRoot s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ j))‖ ≤ q) ∧
            (∀ i j,
              ‖pairKernel
                (selectedContinuedRoot s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ i))
                (selectedContinuedRoot s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ j))‖ ≤
                1+C/(N:ℝ)) := by
  classical
  obtain ⟨b,r,hb,hr,hbranch⟩ := selected_disk_true_branch d
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  let η₀ := min ηA (Real.sin d.thetaB/4)
  let τ₀ := min r (min (1/2:ℝ) ((1+Real.cos d.thetaB)/8))
  refine ⟨η₀,τ₀,lt_min hηA (by positivity),lt_min hr (lt_min (by norm_num) (by positivity)),?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall : η ≤ Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  have hηA' : η ≤ ηA := hηlt.le.trans (min_le_left _ _)
  have hτr : τ < r := hτlt.trans_le (min_le_left _ _)
  have hτsmall : 2*τ ≤ 1 := by
    have hh := hτlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτS : 4*τ < 1+Real.cos d.thetaB := by
    have hh := hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨cB,hcB,hB⟩ := hbranch τ hτ hτr
  obtain ⟨epsG,hepsG,Z,hZ,hphys,hZcover,g,q,hg,hq,hq1,hgroups,hsame,_hcross⟩ :=
    selected_compact_root_groups d hcsmall hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨epsW,hepsW,K,hK,hKD,_hKi,hWcover⟩ :=
    selected_regular_physical_compact d hcsmall hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨cW,L,hcW,hL,hmotion⟩ := continuedRoot_compact_motion hK hKD
  let B : ℝ := 4/g+12/g^2
  have hBpos : 0 < B := by dsimp [B]; positivity
  let Dcap := min 1 (min (g/6) ((1-q)/(2*B)))
  have hDcap : 0 < Dcap := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let c := min cB (min (1/4:ℝ) (min (cW/3) (Dcap/(3*L))))
  let D := 3*L*c
  let eps₀ := min epsG (min epsW (min r 1))
  have hc : 0 < c := lt_min hcB (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hD : 0 < D := by dsimp [D]; positivity
  have hDc : D ≤ Dcap := by
    have hc' : c ≤ Dcap/(3*L) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 3*L)).mp hc'
    dsimp [D]
    nlinarith only [hh]
  have hD1 : D ≤ 1 := hDc.trans (min_le_left _ _)
  have hDg : D ≤ g/6 := hDc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDq : B*D ≤ (1-q)/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*B)).mp
      (hDc.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hh]
  have hcB' : c ≤ cB := min_le_left _ _
  have hcquarter : c ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcW' : c ≤ cW/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨c,eps₀,B*D,(1+q)/2,hc,lt_min hepsG (lt_min hepsW (lt_min hr zero_lt_one)),
    mul_pos hBpos hD,by linarith,by linarith,?_⟩
  intro N eps θ s hN heps hepslt hθ hsupport hsd
  let f := constructedSelector d.thetaB η α
  let P := occupancy (fun i => f.p (θ i))
  let ρ := P/(N:ℝ)
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ 1 θ
  let W₀ : Fin N → ℂ := fun i => sourceW (radialParameter d.theta eps) (y i)
  let W : Fin N → ℂ := fun i => sourceW s (y i)
  let J := selectedCompactIndexSet d.thetaB η θ
  let z : Fin N → ℂ := fun i => continuedRoot (W i)
  let z₀ : Fin N → ℂ := fun i => if i ∈ J then continuedRoot (W₀ i) else z i
  let color : Fin N → Bool := fun i => decide (‖z₀ i‖ ≤ 1-g)
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hepsG' : eps < epsG := hepslt.trans_le (min_le_left _ _)
  have hepsW' : eps < epsW := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsr : eps < r := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hp0 : ∀ x, 0 ≤ f.p x := fun x => (thresholdStep_range _ _ _).1
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  obtain ⟨k,hk⟩ := selected_tsupport_named f θ hsupport
  obtain ⟨hkp,_hkm,_hks,_hkc⟩ := constructed_named_support hsinb hη hηsmall hα hk
  have hP : 1 ≤ P := occupancy_named (fun i => hp0 (θ i)) k hkp
  have hPN : P ≤ N := occupancy_le (fun i => hp1 (θ i))
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := (div_le_one hn0).mpr hPN
  have hWform (i : Fin N) : W₀ i=selectedCenterW d.theta d.c₀ f τ eps ρ (θ i) := by
    change sourceW _ (y i)=_
    rw [show y i=radialAnglePoint (-d.c₀*eps+selectedLimitingShift f τ ρ (θ i)) (θ i) from
      deformedPoint_selected_formula f d.c₀ eps τ θ i]
    rfl
  have hJmem (i : Fin N) : i ∈ J ↔ η^2/2 ≤ lowerChord d.thetaB (θ i) := by
    simp [J,selectedCompactIndexSet]
  have hparam (i : Fin N) (hi : i ∈ J) : (ρ,θ i) ∈ selectedCompactParameters d.thetaB η :=
    ⟨⟨hρ0,hρ1⟩,⟨⟨hθ.1 i,hθ.2 i⟩,(hJmem i).mp hi⟩⟩
  have hbaseK (i : Fin N) (hi : i ∈ J) : z₀ i ∈ Z := by
    simp [z₀,hi]
    rw [hWform]
    exact hZcover eps heps hepsG' (ρ,θ i) (hparam i hi)
  have hcenterK (i : Fin N) (hi : i ∈ J) : W₀ i ∈ K := by
    rw [hWform]
    exact hWcover eps heps hepsW' (ρ,θ i) (hparam i hi)
  have hsmall : ‖s-radialParameter d.theta eps‖ < (1:ℝ)/2 := by
    have hh : c/(N:ℝ) ≤ c := div_le_self hc.le hn
    linarith only [hsd,hh,hcquarter]
  have hnorm : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
  have hsn := norm_ge_half_of_near_unit hnorm hsmall
  have hdiff (i : Fin N) : ‖W i-W₀ i‖ ≤ 3*c/(N:ℝ) := by
    have he : W i-W₀ i=sourceS s-sourceS (radialParameter d.theta eps) := by dsimp [W,W₀,sourceW]; ring
    rw [he]
    calc
      _ ≤ 3*‖s-radialParameter d.theta eps‖ := sourceS_sub_norm_le hsn hnorm
      _ ≤ 3*(c/(N:ℝ)) := mul_le_mul_of_nonneg_left hsd (by norm_num)
      _ = _ := by ring
  have hdiffc : 3*c/(N:ℝ) ≤ cW := by
    have hh : 3*c/(N:ℝ) ≤ 3*c := div_le_self (by positivity) hn
    linarith only [hh,hcW']
  have hbranch (i : Fin N) (hi : i ∉ J) : ‖z i‖ ≤ 1 ∧ (z i).im ≤ 0 := by
    have hic : ¬ η^2/2 ≤ lowerChord d.thetaB (θ i) := fun h => hi ((hJmem i).mpr h)
    have hch : lowerChord d.thetaB (θ i) ≤ η^2 := by linarith [sq_nonneg η]
    obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau hsinb hη hηsmall hα hch
    let u := θ i+d.thetaB-2*Real.pi
    have hu : |u| < r := hcoord (θ i) (hθ.1 i) (hθ.2 i)
      (hch.trans (pow_le_pow_left₀ hη.le hηA' 2))
    have hyp : y i=plateauY d.c₀ eps τ ρ d.thetaB u :=
      deformedPoint_selected_plateau f d.thetaB d.c₀ eps τ θ i hpi hmi
    have hsB := hsd.trans (div_le_div_of_nonneg_right hcB' hn0.le)
    have hbnd := (hB N eps P u s hN heps hepsr hP hPN hu hsB).1
    have hWi : 0 < (W i).im := by
      change 0 < (sourceW s (y i)).im
      rw [hyp]
      exact lt_of_lt_of_le (by positivity : 0 < b*(eps+τ*ρ)) hbnd
    dsimp only [z]
    rw [continuedRoot_eq_interiorRoot hWi]
    exact ⟨(interiorRoot_norm_lt_one hWi).le,(interiorRoot_lower_im hWi).le⟩
  have hbase (i : Fin N) : ‖z₀ i‖ ≤ 1 ∧ (z₀ i).im ≤ 0 := by
    by_cases hi : i ∈ J
    · exact ⟨(hphys _ (hbaseK i hi)).1,(hphys _ (hbaseK i hi)).2.1⟩
    · simpa only [z₀,hi,ite_false] using hbranch i hi
  have hmov (i : Fin N) : ‖z i-z₀ i‖ ≤ D/(N:ℝ) := by
    by_cases hi : i ∈ J
    · have hm := (hmotion (W₀ i) (hcenterK i hi) (W i) ((hdiff i).trans hdiffc)).2
      have hh := hm.trans (mul_le_mul_of_nonneg_left (hdiff i) hL.le)
      have he : L*(3*c/(N:ℝ))=D/(N:ℝ) := by dsimp [D]; ring
      simpa only [z,z₀,hi,ite_true] using hh.trans_eq he
    · simp only [z₀,hi,ite_false,sub_self,norm_zero]
      positivity
  have hcov (i : Fin N) (hi : i ∈ J) : ‖z₀ i‖ ≤ 1-g ∨ (z₀ i).im ≤ -g := hgroups _ (hbaseK i hi)
  have hsame' : ∀ i ∈ J, ∀ j ∈ J, color i=color j → ‖pairKernel (z₀ i) (z₀ j)‖ ≤ q := by
    intro i hi j hj hcol
    apply hsame _ (hbaseK i hi) _ (hbaseK j hj)
    by_cases hni : ‖z₀ i‖ ≤ 1-g
    · have hnj : ‖z₀ j‖ ≤ 1-g := by simpa [color,hni] using hcol.symm
      exact Or.inl ⟨hni,hnj⟩
    · have hnj : ¬ ‖z₀ j‖ ≤ 1-g := by simpa [color,hni] using hcol.symm
      exact Or.inr ⟨(hcov i hi).resolve_left hni,(hcov j hj).resolve_left hnj⟩
  obtain ⟨hsameDisk,hgeneral,hbranchPair⟩ := compact_perturbed_pair_bounds hN J color z₀ z hg hq1 hD.le
    hD1 hDg hDq (fun i => (hbase i).1) (fun i => (hbase i).2) hcov hsame' hmov
    (fun i hi => by simp [z₀,hi])
  refine ⟨color,hsameDisk,?_⟩
  intro i j
  by_cases hi : i ∈ J
  · exact hgeneral i j (Or.inl hi)
  · by_cases hj : j ∈ J
    · exact hgeneral i j (Or.inr hj)
    · exact (hbranchPair i hi j hj).trans (le_add_of_nonneg_right (by positivity))

end
end IsingBulk.Tail
