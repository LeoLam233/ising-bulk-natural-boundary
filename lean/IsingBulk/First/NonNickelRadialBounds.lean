import IsingBulk.First.NonNickelGeometry
import IsingBulk.First.ComplementGlobalBound
import IsingBulk.First.RadiusIndependence

/-! Internal fixed-order non-Nickel bounds on the actual offsite double
contour. The radius is selected at the evaluation point and is held fixed
under every complex s derivative. No full-site literature premise is used. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology ContDiff

theorem doubleFormFactor_iteratedDeriv_localized_one (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (doubleFormFactor N r) s =
      iteratedDeriv j (fun t => localizedDoubleFormFactor N r t (fun _ => 1)) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  apply doubleFormFactor_eq_product_integral N hN r t (globalRoot t)
  intro θ
  exact (globalRoot_admissible hr hr1 ht.2).toTuple N _
    (fun _ => anglePoint_norm hr.le _)

/-- For each fixed N one positive radial interval works for every finite
derivative order, with an order-dependent bound. This is a radial theorem,
not the stronger published neighborhood/variable-radius statement. -/
theorem nonNickel_fixed_radius_radial_bound {N : ℕ} (hN : 0 < N)
    (S θ : ℝ) (hlevel : 0 < S ∧ S < 2) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) = (S:ℂ))
    (hn : ¬ PrimeFamily.NickelAt (Complex.exp ((θ:ℂ)*Complex.I)) N) :
    ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ,
      0 < ε → ε ≤ e →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair θ ε).1))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  have hsep (u : DoubleAngularVector N) (_hu : u ∈ tsupport (fun _ : DoubleAngularVector N => (1:ℝ))) :
      ActiveSourceSeparated (angleTuple 1 u.1) (angleTuple 1 u.2) S :=
    nonNickel_active_separated hN (fun _ => anglePoint_norm (by norm_num) _)
      (fun _ => anglePoint_norm (by norm_num) _) hlevel
      (Complex.norm_exp_ofReal_mul_I _) hS hn
  have hper : DoubleCoordinatePeriodic (fun _ : DoubleAngularVector N => (1:ℝ)) := by
    intro u i
    exact ⟨rfl,rfl⟩
  obtain ⟨e,he,hB⟩ := source_complement_global_bound hN S θ hθ hS
    (fun _ => 1) contDiff_const hper hsep
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  refine ⟨min e (d/2),lt_min he (by positivity),?_⟩
  intro j
  obtain ⟨C,hC,hb⟩ := hB j
  refine ⟨C,hC,?_⟩
  intro ε hε hεsmall
  have hεe := hεsmall.trans (min_le_left e (d/2))
  have hεd : ε < d := hεsmall.trans_lt ((min_le_right e (d/2)).trans_lt (by linarith))
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter θ ε)
    (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) hε)).2
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  rw [← iteratedDeriv_eq_iterate,
    doubleFormFactor_iteratedDeriv_localized_one N hN j hr hr1
      (s := (sourceRadialPair θ ε).2) hmargin,
    iteratedDeriv_eq_iterate]
  exact hb ε hε hεe

end
end IsingBulk.First
