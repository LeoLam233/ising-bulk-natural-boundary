import IsingBulk.AnisoF002.C03.NegativeFullSeriesGrowth
import IsingBulk.AnisoF002.C03.NegativeCompleteMiddleAttachment
import IsingBulk.AnisoF002.C03.RegularPhysicalParticleTails
import IsingBulk.AnisoF002.C03.NegativeBoundaryAnalyticity

/-!
# Full physical negative-HT Taylor-series noncancellation

Every middle particle and winding, both infinite outside ranges and the
complete analytic remainder are constructed from the original local
physical data. The exact full odd Taylor series beats every geometric
bound. No coefficient-identification, tail or noncancellation premise
is added to the physical data.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

theorem negative_physical_full_taylor_growth {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) {a p : ℕ}
    (hp : Odd p) (hcop : a.Coprime p) (hphase : φ = 2 * Real.pi * a / p) :
    ∀ M R : ℝ, 0 < M → 0 < R → ∃ j : ℕ,
      M / R ^ j < ‖∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n‖ := by
  obtain ⟨s0, hs0, hζ, hmiddle⟩ :=
    exists_complete_actual_middle_attachment hb hB hφ hπ hBi hbsq hp hcop hphase
  obtain ⟨r, s, Mi, ki, A, hs, hr, hss, hMi, _, _, D, _, _, hcomplete, houtside⟩ :=
    exists_actual_complete_particle_tail_data hs0 hb hB hφ hπ hBi hbsq hp hcop hphase
  obtain ⟨T, _, hattach⟩ := hmiddle s hs hss r Mi ki hr hMi.le
  let P : ℕ → ℕ → ℂ := fun j q => innerCyclePoleCoefficient (D (resonantOddIndex p q)) j
  let rem : ℕ → ℂ := completeBoundaryAnalyticRemainder D hs.le
  have hP (j : ℕ) : Summable fun q => ‖P j q‖ := by
    have hh := (hcomplete j).1.comp_injective (resonantOddIndex_injective hp.pos)
    apply hh.congr
    intro q
    exact congrArg norm (completeCyclePoleCoefficient_resonant_eq hp hcop hphase D j q)
  have hrem (j : ℕ) : ‖rem j‖ ≤ Real.exp (completeAnalyticExponent A j) :=
    (hcomplete j).2.2.1
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heventually : ∀ᶠ j : ℕ in atTop,
      (∀ q ∈ resonantMiddleIndices p j,
        ‖P j q - (Complex.sqrt (B 0) / b 0) *
            resonantFullModelCoefficient B (Real.cos φ) (Real.sin φ) p j q‖ ≤
          ‖resonantFullModelCoefficient B (Real.cos φ) (Real.sin φ) p j q‖ / 16) ∧
      (∑' q : ℕ, ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ) else P j q‖) ≤
        Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) +
          Real.exp (completeHighExponent A j) := by
    filter_upwards [houtside, hlog.eventually (eventually_ge_atTop T)] with j hj ht
    exact ⟨fun q hq => hattach D j ht q hq, hj.2⟩
  have hgrowth := full_residue_taylor_growth_from_complete_bounds hB
    (show B 0 ∈ Complex.slitPlane from Or.inr hBi.ne) (Real.cos φ)
    (Real.sin_pos_of_pos_of_lt_pi hφ hπ) hp P rem (Complex.sqrt (B 0) / b 0) hζ A
    hP hrem heventually
  intro M R hM hR
  obtain ⟨j, hj⟩ := hgrowth M R hM hR
  refine ⟨j, ?_⟩
  rw [(hcomplete j).2.2.2, completeCyclePoleCoefficient_tsum_resonant hp hcop hphase D j]
  exact hj

theorem negative_physical_odd_sum_no_analytic_inward_germ {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) {a p : ℕ}
    (hp : Odd p) (hcop : a.Coprime p) (hphase : φ = 2 * Real.pi * a / p) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        negativePhysicalOddSum b B φ =ᶠ[𝓝 (-(eps : ℂ))] g :=
  no_analytic_inward_germ_of_actual_taylor_growth hb hB hφ hπ hBi hbsq
    (negative_physical_full_taylor_growth hb hB hφ hπ hBi hbsq hp hcop hphase)

end
end IsingBulk.AnisoF002.NegativeHT
