import IsingBulk.AnisoF002.C03.IsotropicShellProductMeasure
import IsingBulk.AnisoF002.C03.IsotropicConstrainedChart
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compact genuine extreme cells in the original constrained coordinates

The first and last angles vary on the actual constraint-preserving
fiber; all remaining coordinates are free Lebesgue coordinates. The
cell keeps every rectangle, extremum and shell condition. Compactness
and genuine joint continuity establish integrability before Fubini.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def extremeFiberAngles {n : ℕ} (a : ℝ) (p : ℝ × (Fin n → ℝ)) : Fin (n + 2) → ℝ :=
  constrainedAngleLine (extremeFiberBase a p.2) 0 (Fin.last (n + 1)) p.1

theorem extremeFiberAngles_first {n : ℕ} (a : ℝ) (p : ℝ × (Fin n → ℝ)) :
    extremeFiberAngles a p 0 = p.1 := by
  rw [extremeFiberAngles, constrainedAngleLine_first]
  · simp
  · exact Fin.ne_of_val_ne (by simp)

theorem extremeFiberAngles_middle {n : ℕ} (a : ℝ) (p : ℝ × (Fin n → ℝ)) (k : Fin n) :
    extremeFiberAngles a p k.succ.castSucc = p.2 k := by
  rw [extremeFiberAngles, constrainedAngleLine_other]
  · exact extremeFiberBase_middle a p.2 k
  · exact Fin.ne_of_val_ne (by simp)
  · exact Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega)

theorem extremeFiberAngles_last {n : ℕ} (a : ℝ) (p : ℝ × (Fin n → ℝ)) :
    extremeFiberAngles a p (Fin.last (n + 1)) = a - p.1 - ∑ k, p.2 k := by
  rw [extremeFiberAngles, constrainedAngleLine_last]
  · rw [extremeFiberBase_last]
    ring
  · exact Fin.ne_of_val_ne (by simp)

theorem extremeFiberAngles_eq_snoc {n : ℕ} (a : ℝ) (p : ℝ × (Fin n → ℝ)) :
    extremeFiberAngles a p = Fin.snoc (Fin.cons p.1 p.2) (a - p.1 - ∑ k, p.2 k) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [extremeFiberAngles_last, Fin.snoc_last]
  · refine Fin.cases ?_ (fun l => ?_) j
    · rw [Fin.snoc_castSucc, Fin.cons_zero]
      exact extremeFiberAngles_first a p
    · simp only [extremeFiberAngles_middle, Fin.snoc_castSucc, Fin.cons_succ]

theorem extremeFiberAngles_continuous {n : ℕ} (a : ℝ) :
    Continuous (extremeFiberAngles (n := n) a) := by
  rw [show extremeFiberAngles (n := n) a =
    (fun p : ℝ × (Fin n → ℝ) => Fin.snoc (Fin.cons p.1 p.2) (a - p.1 - ∑ k, p.2 k))
    from funext (extremeFiberAngles_eq_snoc a)]
  apply Continuous.finSnoc (A := fun _ : Fin (n + 2) => ℝ)
  · exact continuous_fst.finCons (A := fun _ : Fin (n + 1) => ℝ) continuous_snd
  · exact (continuous_const.sub continuous_fst).sub
      (continuous_finsetSum _ (fun k _ => (continuous_apply k).comp continuous_snd))

def actualExtremeCell (n : ℕ) (a b δ r : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {p | p.1 ∈ fullExtremeFiber (extremeFiberBase a p.2) 0 (Fin.last (n + 1)) b δ r}

theorem actualExtremeCell_isClosed (n : ℕ) (a b δ r : ℝ) :
    IsClosed (actualExtremeCell n a b δ r) := by
  have hk (k : Fin (n + 2)) : Continuous (fun p : ℝ × (Fin n → ℝ) => extremeFiberAngles a p k) :=
    (continuous_apply k).comp (extremeFiberAngles_continuous a)
  change IsClosed {p : ℝ × (Fin n → ℝ) |
    (∀ k, extremeFiberAngles a p k ∈ Icc (-(b + δ)) δ) ∧
    (∀ k, extremeFiberAngles a p 0 ≤ extremeFiberAngles a p k) ∧
    (∀ k, extremeFiberAngles a p k ≤ extremeFiberAngles a p (Fin.last (n + 1))) ∧
    r ≤ extremeFiberAngles a p (Fin.last (n + 1)) - extremeFiberAngles a p 0 ∧
    extremeFiberAngles a p (Fin.last (n + 1)) - extremeFiberAngles a p 0 ≤ 2 * r}
  simp only [mem_Icc, ofPred_and, ofPred_forall]
  exact (isClosed_iInter (fun k => (isClosed_le continuous_const (hk k)).inter
      (isClosed_le (hk k) continuous_const))).inter
    ((isClosed_iInter (fun k => isClosed_le (hk 0) (hk k))).inter
      ((isClosed_iInter (fun k => isClosed_le (hk k) (hk (Fin.last (n + 1))))).inter
        ((isClosed_le continuous_const ((hk (Fin.last (n + 1))).sub (hk 0))).inter
          (isClosed_le ((hk (Fin.last (n + 1))).sub (hk 0)) continuous_const))))

theorem actualExtremeCell_isCompact (n : ℕ) (a b δ r : ℝ) :
    IsCompact (actualExtremeCell n a b δ r) := by
  apply isCompact_Icc.of_isClosed_subset (actualExtremeCell_isClosed n a b δ r)
    (s := Icc ((-b - δ), fun _ : Fin n => -b - δ) (δ, fun _ : Fin n => δ))
  intro p hp
  have hfirst := hp.1 0
  change extremeFiberAngles a p 0 ∈ _ at hfirst
  rw [extremeFiberAngles_first] at hfirst
  have hmiddle (k : Fin n) := hp.1 k.succ.castSucc
  have hm (k : Fin n) : -b - δ ≤ p.2 k ∧ p.2 k ≤ δ := by
    have hh := hmiddle k
    change extremeFiberAngles a p k.succ.castSucc ∈ _ at hh
    rw [extremeFiberAngles_middle] at hh
    exact ⟨by linarith only [hh.1], hh.2⟩
  exact ⟨⟨by linarith only [hfirst.1], fun k => (hm k).1⟩,
    ⟨hfirst.2, fun k => (hm k).2⟩⟩

theorem actualExtremeCell_remaining_mem {n : ℕ} (μ b δ r : ℝ)
    (p : ℝ × (Fin n → ℝ))
    (hp : p ∈ actualExtremeCell n ((n + 2 : ℝ) * (μ - b)) b δ r) :
    p.2 ∈ remainingAngularBox n μ b r := by
  let θ := extremeFiberAngles ((n + 2 : ℝ) * (μ - b)) p
  have hdiam (k l : Fin (n + 2)) : |(θ k + b) - (θ l + b)| ≤ 2 * r := by
    have hki := hp.2.1 k
    have hli := hp.2.1 l
    have hkj := hp.2.2.1 k
    have hlj := hp.2.2.1 l
    have hgap := hp.2.2.2.2
    change θ 0 ≤ θ k at hki
    change θ 0 ≤ θ l at hli
    change θ k ≤ θ (Fin.last (n + 1)) at hkj
    change θ l ≤ θ (Fin.last (n + 1)) at hlj
    change θ (Fin.last (n + 1)) - θ 0 ≤ 2 * r at hgap
    exact abs_le.mpr ⟨by linarith only [hki, hli, hkj, hlj, hgap],
      by linarith only [hki, hli, hkj, hlj, hgap]⟩
  have hmean : angularMean (fun k => θ k + b) = μ := by
    rw [show θ = constrainedAngleLine (extremeFiberBase ((n + 2 : ℝ) * (μ - b)) p.2)
      0 (Fin.last (n + 1)) p.1 from rfl, constrainedAngleLine_shifted_mean,
      extremeFiberBase_shifted_mean]
  have hcoord (k : Fin n) : |p.2 k + b - μ| ≤ 2 * r := by
    have hh := angularMean_distance_bound (show 0 < n + 2 by omega)
      (fun k => θ k + b) (2 * r) hdiam k.succ.castSucc
    rw [hmean] at hh
    simpa only [θ, extremeFiberAngles_middle] using hh
  exact ⟨fun k => by linarith only [(abs_le.mp (hcoord k)).1],
    fun k => by linarith only [(abs_le.mp (hcoord k)).2]⟩

theorem actualFullPhaseDensity_angles_continuous {N : ℕ}
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (i : Fin N) : Continuous (actualFullPhaseDensity (N := N) s η τ ξ γ) := by
  have hG : Continuous (fun θ : Fin N → ℝ => actualTotalPhase η τ ξ (s, θ) - (γ : ℂ)) :=
    (actualTotalPhase_angles_contDiff s hs η τ ξ hη hτ hξ 0).continuous.sub continuous_const
  have hden (θ : Fin N → ℝ) : 1 - Complex.exp (-Complex.I *
      (actualTotalPhase η τ ξ (s, θ) - (γ : ℂ))) ≠ 0 := by
    apply complex_phase_denominator_ne_zero
    have hlocal := upperPhysicalPhase_im_neg _
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i)
    have hsum := actualTotalPhase_attenuation_ge_individual s hs η τ ξ hη hτ hξ θ i
    change (actualPhysicalPhase η τ ξ (s, θ) i).im < 0 at hlocal
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith only [hlocal, hsum]
  apply Continuous.div
  · apply continuous_finsetProd
    intro k _
    exact (continuous_const.add (actualPhaseSlope_angles_continuous s hs η τ ξ hη hτ hξ k)).norm
  · exact (continuous_const.sub (Complex.continuous_exp.comp (continuous_const.mul hG))).norm
  · exact fun θ => norm_ne_zero_iff.mpr (hden θ)

theorem actualExtremeCell_density_integrable (n : ℕ) (a b δ r : ℝ)
    (s : ℂ) (hs : 0 < s.im) (η τ ξ γ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    IntegrableOn (fun p : ℝ × (Fin n → ℝ) => actualFullPhaseDensity s η τ ξ γ (extremeFiberAngles a p))
      (actualExtremeCell n a b δ r) volume := by
  exact ((actualFullPhaseDensity_angles_continuous s hs η τ ξ γ hη hτ hξ 0).comp
    (extremeFiberAngles_continuous a)).continuousOn.integrableOn_compact
    (actualExtremeCell_isCompact n a b δ r)

end IsingBulk.AnisoF002.Isotropic
