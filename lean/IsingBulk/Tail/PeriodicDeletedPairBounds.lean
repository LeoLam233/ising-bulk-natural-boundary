import IsingBulk.Tail.MixedDeletedPairSource
import IsingBulk.Tail.CompactCompletePairJets
import IsingBulk.Tail.MixedSectorWeights
import IsingBulk.First.PeriodicWrapInvariant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem periodic_bound_on_tsupport {N : ℕ} (W F : (Fin N → ℝ) → ℝ) (B : ℝ)
    (hW : ∀ x i, W (Function.update x i (x i+2*Real.pi))=W x)
    (hF : ∀ x i, F (Function.update x i (x i+2*Real.pi))=F x) (hc : Continuous F)
    (hb : ∀ x ∈ angleBox N, x ∈ tsupport W → F x ≤ B) :
    ∀ x ∈ tsupport W, F x ≤ B := by
  apply closure_minimal _ (isClosed_le hc continuous_const)
  intro x hx
  let y := centeredWrap (fun _ => Real.pi) x
  have hyW : W y ≠ 0 := by
    change W (centeredWrap (fun _ => Real.pi) x) ≠ 0
    rwa [coordinatePeriodic_centeredWrap W hW]
  have hh := hb y (centeredWrap_pi_mem_angleBox x) (subset_closure hyW)
  rwa [coordinatePeriodic_centeredWrap F hF] at hh

def actualDeletedPairNorm {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (E : Finset (Fin N × Fin N)) (θ : Fin N → ℝ) : ℝ :=
  let y := deformedPoint f r τ lam θ
  ∏ ij ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
    ‖canceledPair (y ij.1) (y ij.2) (globalRoot s (y ij.1)) (globalRoot s (y ij.2))‖

theorem actualDeletedPairNorm_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) (s : ℂ) (E : Finset (Fin N × Fin N)) (θ : Fin N → ℝ) (i : Fin N) :
    actualDeletedPairNorm f r τ lam s E (Function.update θ i (θ i+2*Real.pi))=
      actualDeletedPairNorm f r τ lam s E θ := by
  unfold actualDeletedPairNorm
  rw [deformedPoint_periodic f hf]

theorem actualDeletedPairNorm_continuous {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (E : Finset (Fin N × Fin N)) :
    Continuous (actualDeletedPairNorm f r τ lam s E) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hy (i : Fin N) := (deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth i).continuous.continuousAt (x := θ)
  have hz (i : Fin N) : ContinuousAt (fun x => globalRoot s (deformedPoint f r τ lam x i)) θ :=
    (((compactSource_root_smooth hN f hf hr hr1 hτ hlam i) (s,θ) ⟨hs,mem_univ _⟩).1.continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hzn (i : Fin N) : ‖globalRoot s (deformedPoint f r τ lam θ i)‖ < 1 :=
    interiorRoot_norm_lt_one (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam hs θ i)
  unfold actualDeletedPairNorm
  apply tendsto_finsetProd
  intro ij hij
  exact (continuousAt_canceledPair _ _ _ _ θ (hy ij.1) (hy ij.2) (hz ij.1) (hz ij.2)
    (deformedPoint_nonzero f hr.ne' τ lam θ ij.1) (deformedPoint_nonzero f hr.ne' τ lam θ ij.2)
    (one_sub_mul_ne_zero_of_norm_lt_one (hzn ij.1) (hzn ij.2))).norm

/-- A periodic source bound proved on its fundamental box also controls every
signed lift. The only continuity used is at fixed physical parameter. -/
theorem actual_deleted_pairs_all_angles {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (E : Finset (Fin N × Fin N))
    (W : (Fin N → ℝ) → ℝ) (hW : ∀ x i, W (Function.update x i (x i+2*Real.pi))=W x)
    (B : ℝ) (hb : ∀ θ ∈ angleBox N, θ ∈ tsupport W → actualDeletedPairNorm f r τ lam s E θ ≤ B) :
    ∀ θ ∈ tsupport W, actualDeletedPairNorm f r τ lam s E θ ≤ B :=
  periodic_bound_on_tsupport W _ B hW (actualDeletedPairNorm_periodic f hf r τ lam s E)
    (actualDeletedPairNorm_continuous hN f hf hr hr1 hτ hlam hs E) hb

end
end IsingBulk.Tail
