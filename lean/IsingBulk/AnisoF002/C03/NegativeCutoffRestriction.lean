import IsingBulk.AnisoF002.C03.NegativeInnerMeasurableRemainder

/-!
# Freely shrinking the actual fixed angular cutoff

The pole and literal analytic remainder are unchanged on the smaller
real-cycle set.  This lets independent physical estimates share one
cutoff chosen before any particle population.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

def InnerRemainderFamily.restrictCutoff {b B : ℂ → ℂ} {φ r s s' M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ n r s M kappa) (hss : s' ≤ s) :
    InnerRemainderFamily b B φ n r s' M kappa where
  pole := d.pole
  pole_continuous := d.pole_continuous.mono (fun _ h => h.trans hss)
  remainder := fun t q => d.remainder t ⟨q.1, q.2.trans hss⟩
  remainder_measurable := by
    have hc : Continuous (fun p : ℂ × InnerAngularSet n s' =>
        (p.1, (⟨p.2.1, p.2.2.trans hss⟩ : InnerAngularSet n s))) :=
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk (fun p => p.2.2.trans hss))
    exact d.remainder_measurable.comp hc.measurable
  pole_zero := fun q => d.pole_zero ⟨q.1, q.2.trans hss⟩
  pole_bound := fun q => d.pole_bound ⟨q.1, q.2.trans hss⟩
  residue_denominator_ne_zero := fun q => d.residue_denominator_ne_zero ⟨q.1, q.2.trans hss⟩
  remainder_analytic := fun q => d.remainder_analytic ⟨q.1, q.2.trans hss⟩
  remainder_bound := fun q => d.remainder_bound ⟨q.1, q.2.trans hss⟩
  exact_remainder := fun q => d.exact_remainder ⟨q.1, q.2.trans hss⟩
  exact_density := fun hres q => d.exact_density hres ⟨q.1, q.2.trans hss⟩

theorem exists_actual_inner_remainder_families_below_cutoff {b B : ℂ → ℂ} {φ epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s M kappa : ℝ, 0 < r ∧ 0 < s ∧ s ≤ epsilon ∧ 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, 0 < n → Nonempty (InnerRemainderFamily b B φ n r s M kappa) := by
  obtain ⟨r, s, M, kappa, hr, hs, hM, hk, hd⟩ :=
    exists_actual_inner_remainder_families hb hB hφ hπ hBi hbsq
  refine ⟨r, min s epsilon, M, kappa, hr, lt_min hs hepsilon, min_le_right _ _, hM, hk, ?_⟩
  intro n hn
  obtain ⟨d⟩ := hd n hn
  exact ⟨d.restrictCutoff (min_le_left _ _)⟩

end
end IsingBulk.AnisoF002.NegativeHT
