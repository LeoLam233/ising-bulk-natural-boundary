import IsingBulk.Tail.SupportedLieRegularity
import IsingBulk.Tail.PeriodicLieStages

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set MeasureTheory
open scoped Topology ContDiff

theorem supported_periodic_lie_integral {n : ℕ} {Ω : Set (ℂ × AngularSpace n)} {U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (D : ℂ → AngularSpace n → ℂ)
    (w : AngularSpace n → ℂ) (hw : ContDiff ℝ ∞ w)
    (hD : ParameterSmoothOn Ω D) (hV : ∀ i,ParameterSmoothOn Ω (fun s x => V s x i))
    (hcover : U ×ˢ tsupport w⊆Ω)
    (hwper : CoordinatePeriodic (n+1) w)
    (hDper : ∀ s,CoordinatePeriodic (n+1) (D s))
    (hVper : ∀ s i,CoordinatePeriodic (n+1) (fun x => V s x i)) (k : ℕ) :
    EqOn (fun s => ∫ x in angleBox (n+1),((lieStep V)^[k] (fun s x => w x*D s x)) s x)
      (deriv^[k] (fun s => ∫ x in angleBox (n+1),w x*D s x)) U ∧
      ∀ s∈U,IntegrableOn (((lieStep V)^[k] (fun s x => w x*D s x)) s) (angleBox (n+1)) := by
  let A := fun s x => w x*D s x
  have hreg (j : ℕ) := supported_weighted_lie_stages_regular hΩ U V D w hw hD hV hcover j
  have hper (j : ℕ) : ∀ s,CoordinatePeriodic (n+1) (((lieStep V)^[j] A) s) :=
    coordinatePeriodic_iterate_lieStep V A hVper (fun s => coordinatePeriodic_mul hwper (hDper s)) j
  have hOpen : IsOpen (U ×ˢ (Set.univ : Set (AngularSpace n))) := hU.prod isOpen_univ
  have hsub : U ×ˢ angleBox (n+1)⊆U ×ˢ (Set.univ : Set (AngularSpace n)) := fun p hp => ⟨hp.1,mem_univ _⟩
  have hcont (j : ℕ) : ContinuousOn (fun p : ℂ × AngularSpace n => ((lieStep V)^[j] A) p.1 p.2)
      (U ×ˢ angleBox (n+1)) := (hreg j).1.continuousOn.mono hsub
  refine ⟨periodic_sector_iterate_lieStep_integral_on hU V A k
    (fun j _ => hcont j) ?_ ?_ ?_ ?_,?_⟩
  · intro j _
    exact ((hreg j).1.paramDeriv hOpen).continuousOn.mono hsub
  · intro j _ s hs x _
    exact ((hreg j).1 (s,x) ⟨hs,mem_univ _⟩).2
  · intro j _ s hs i
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((((hreg j).2 i (s,x) ⟨hs,mem_univ _⟩).1).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  · intro j _ s _ i
    exact coordinatePeriodic_mul (hVper s i) (hper j s)
  · intro s hs
    exact ((hcont k).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hs,hx⟩)).integrableOn_compact isCompact_Icc

end
end IsingBulk.Tail
