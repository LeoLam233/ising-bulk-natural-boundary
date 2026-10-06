import IsingBulk.Tail.OriginalPairSupport
import IsingBulk.Tail.ProtectedActualBranchPairs

/-! Actual B-by-B complete-pair contraction for the entire real homotopy
on the original c epsilon complex disk. Lambda may equal zero. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem original_current_actual_branch_pair_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0<η₀ ∧ 0<τ₀ ∧
      ∀ η α τ : ℝ, 0<η → η<η₀ → 0<α → α<Real.sin d.thetaB/4 →
        0<τ → τ<τ₀ → ∃ c e : ℝ, 0<c ∧ 0<e ∧
        ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1≤N → 0<eps → eps<e → 0≤lam → lam≤1 → θ∈angleBox N →
          ‖s-radialParameter d.theta eps‖≤c*eps →
          ∀ i j, lowerChord d.thetaB (θ i)<η^2/2 → lowerChord d.thetaB (θ j)<η^2/2 →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          ‖canceledPair (y i) (y j) (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j))‖≤1/2 := by
  obtain ⟨r,hr,hypair⟩ := lower_branch_y_pair_strict d (q := 1/2) (by norm_num)
  obtain ⟨ηA,hηA,hcoord⟩ := lowerChord_small_coordinate d.thetaB_pos d.thetaB_lt hr
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨c,e,hc,_hc1,he,_he1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),r,lt_min hηA (by positivity [d.a_pos]),hr,?_⟩
  intro η α τ hη hηlt hα _hαsmall hτ hτlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  have hηA' := hηlt.le.trans (min_le_left _ _)
  refine ⟨c,min e r,hc,lt_min he hr,?_⟩
  intro N eps lam θ s hN heps hepslt hl0 hl1 hθ hsd i j hi hj
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let P := occupancy (fun i => f.p (θ i))
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hP0 : 0≤P := occupancy_nonneg (fun i => (thresholdStep_range _ _ _).1)
  have hPN : P≤N := occupancy_le (fun i => (thresholdStep_range _ _ _).2)
  have hv0 : 0≤τ*(lam*P/(N:ℝ)) := by positivity
  have hv1 : τ*(lam*P/(N:ℝ))≤τ := by
    apply mul_le_of_le_one_right hτ.le
    apply (div_le_one hn).mpr
    exact (mul_le_of_le_one_left hP0 hl1).trans hPN
  have hcore (k : Fin N) (hk : lowerChord d.thetaB (θ k)<η^2/2) :
      |θ k+d.thetaB-2*Real.pi|<r ∧
      y k=plateauY d.c₀ eps 1 (τ*(lam*P/(N:ℝ))) d.thetaB (θ k+d.thetaB-2*Real.pi) := by
    have hch : lowerChord d.thetaB (θ k)≤η^2 := by linarith [sq_nonneg η]
    obtain ⟨hmi,hpi⟩ := constructed_lower_core_plateau d.a_pos hη hηsmall hα hch
    refine ⟨hcoord (θ k) (hθ.1 k) (hθ.2 k) (hch.trans (pow_le_pow_left₀ hη.le hηA' 2)),?_⟩
    have heq := deformedPoint_current_plateau f d.thetaB d.c₀ eps τ lam θ k hpi hmi
    change y k=plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB (θ k+d.thetaB-2*Real.pi) at heq
    rw [heq]
    unfold plateauY
    congr 1
    push_cast
    ring
  obtain ⟨hui,hyi⟩ := hcore i hi
  obtain ⟨huj,hyj⟩ := hcore j hj
  obtain ⟨hygap,hyp⟩ := hypair eps (τ*(lam*P/(N:ℝ)))
    (θ i+d.thetaB-2*Real.pi) (θ j+d.thetaB-2*Real.pi)
    (by simpa only [abs_of_pos heps] using hepslt.trans_le (min_le_right _ _))
    (by rw [abs_of_nonneg hv0]; exact hv1.trans_lt hτlt) hui huj
  rw [← hyi,← hyj] at hygap hyp
  have hphys (k : Fin N) : 0<(sourceW s (y k)).im := by
    have hb := hupper eps heps (hepslt.trans_le (min_le_left _ _)) s hsd (θ k)
    have hbase : 0<(sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ 0 θ k)).im := by
      simpa only [deformedPoint_coupledRadialExponent,coupledRadialExponent,zero_mul,zero_add,add_zero] using hb
    exact hbase.trans_le (deformed_sourceW_im_ge (by omega) f (Real.exp_pos _) hτ.le hl0 θ s
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.nonneg _)
      (fun x hx => thresholdStep_zero (by linarith) (by linarith))
      (fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x d.a_pos hη hηsmall hx) k)
  have hpz : ‖pairKernel (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j))‖≤1 := by
    rw [show selectedContinuedRoot s (y i)=interiorRoot (sourceW s (y i)) from continuedRoot_eq_interiorRoot (hphys i),
      show selectedContinuedRoot s (y j)=interiorRoot (sourceW s (y j)) from continuedRoot_eq_interiorRoot (hphys j)]
    exact schur_norm_le (interiorRoot_norm_lt_one (hphys i)).le (interiorRoot_norm_lt_one (hphys j)).le
      (mul_nonneg_of_nonpos_of_nonpos (interiorRoot_lower_im (hphys i)).le (interiorRoot_lower_im (hphys j)).le)
  have hquad (a : ℂ) : (selectedContinuedRoot s a)^2-(2*sourceS s-a-a⁻¹)*selectedContinuedRoot s a+1=0 := by
    have hh := continuedRoot_quadratic (sourceW s a)
    dsimp [selectedContinuedRoot,sourceW] at hh ⊢
    linear_combination hh
  have hid := source_pair_identity (deformedPoint_nonzero f (Real.exp_pos _).ne' τ lam θ i)
    (deformedPoint_nonzero f (Real.exp_pos _).ne' τ lam θ j)
    (continuedRoot_nonzero _) (continuedRoot_nonzero _) (hquad (y i)) (hquad (y j)) hygap
    (continuedRoot_pair_gap (Or.inl (Or.inl (hphys i))) (Or.inl (Or.inl (hphys j))))
  change pairKernel (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j))*pairKernel (y i) (y j)=
    canceledPair (y i) (y j) (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j)) at hid
  change ‖canceledPair (y i) (y j) (selectedContinuedRoot s (y i)) (selectedContinuedRoot s (y j))‖≤_
  rw [← hid,norm_mul]
  exact (mul_le_mul_of_nonneg_right hpz (norm_nonneg _)).trans (by simpa only [one_mul] using hyp.le)

end
end IsingBulk.Tail
