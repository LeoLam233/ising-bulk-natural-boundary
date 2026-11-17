import IsingBulk.AnisoF002.C03.NegativeHigherWindingBound
import IsingBulk.AnisoF002.C03.RegularWindingPhysicalModel
import IsingBulk.AnisoF002.C03.RegularWindingPhysicalSectorIdentity

/-!
# The complete physical inner Taylor coefficient versus its exact model

Both first windings and every higher winding are included with their
literal signs.  The shared cutoff is chosen once before particle number,
and the local moving-pole gates are discharged on the actual family.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators Classical

theorem higherWindingSectorIndices_eq_erase (n : ℕ) :
    higherWindingSectorIndices n = ((windingSectorIndices n).erase 1).erase (-1) := by
  ext w
  simp only [higherWindingSectorIndices, Finset.mem_filter, Finset.mem_erase]
  tauto

theorem sum_winding_sectors_first_pair (n : ℕ) (f : ℤ → ℂ) :
    (∑ w ∈ windingSectorIndices n, f w) =
      f 1 + f (-1) + ∑ w ∈ higherWindingSectorIndices n, f w := by
  have h1 : (1 : ℤ) ∈ windingSectorIndices n := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨0, by norm_num⟩⟩ <;> omega
  have hn : (-1 : ℤ) ∈ windingSectorIndices n := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨-1, by norm_num⟩⟩ <;> omega
  have hne : (-1 : ℤ) ∈ (windingSectorIndices n).erase 1 :=
    Finset.mem_erase.mpr ⟨by norm_num, hn⟩
  have he1 := Finset.sum_erase_add (s := windingSectorIndices n) (f := f) h1
  have he2 := Finset.sum_erase_add (s := (windingSectorIndices n).erase 1) (f := f) hne
  rw [higherWindingSectorIndices_eq_erase]
  linear_combination -he1 - he2

theorem winding_sum_error_le_first_pair (n : ℕ) (f : ℤ → ℂ) (z : ℂ) :
    ‖(∑ w ∈ windingSectorIndices n, f w) - z‖ ≤
      ‖f 1 + f (-1) - z‖ + ∑ w ∈ higherWindingSectorIndices n, ‖f w‖ := by
  rw [sum_winding_sectors_first_pair]
  have he : f 1 + f (-1) + (∑ w ∈ higherWindingSectorIndices n, f w) - z =
      (f 1 + f (-1) - z) + ∑ w ∈ higherWindingSectorIndices n, f w := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))

theorem physical_origin_branch_sign_norm {b B : ℂ → ℂ}
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ‖Complex.sqrt (B 0) / b 0‖ = 1 := by
  apply physical_root_branch_sign_norm _ (hbsq 0)
  intro he
  rw [he, Complex.zero_im] at hBi
  exact (lt_irrefl 0) hBi

theorem exists_actual_inner_model_comparison {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s0 M E : ℝ, 0 < s0 ∧ 1 < M ∧ 0 < E ∧
      ‖Complex.sqrt (B 0) / b 0‖ = 1 ∧
      ∀ s : ℝ, 0 < s → s ≤ s0 → ∀ r Mi ki : ℝ, 0 < r → 0 ≤ Mi →
      ∀ᶠ l : ℕ in atTop, ∀ d : InnerRemainderFamily b B φ (2 * l + 1) r s Mi ki,
        ∀ j : ℕ, Complex.exp (-(((2 * l + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
        M * ((2 * l + 1 : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) →
        Real.log (j : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) →
        let model := modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
          (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
            (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
        ‖innerCyclePoleCoefficient d j - (Complex.sqrt (B 0) / b 0) * model‖ ≤
          (E * ((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) + 1 / 32) * ‖model‖ := by
  obtain ⟨c⟩ := exists_physical_winding_residue_control hb hB hφ hπ hBi hbsq
  obtain ⟨Mh, hMh, hhigher⟩ := c.exists_actual_complete_higher_winding_bound hb hB hφ hπ hBi hbsq
  obtain ⟨sf, Mf, E, hsf, hMf, hE, hfirst⟩ := exists_physical_first_pair_model_comparison hb hB hφ hπ hBi hbsq
  obtain ⟨R, si, hR, hsi, hidentity⟩ := exists_actual_winding_sector_identity_radii hb hB hφ hπ hBi hbsq
  let s0 := min c.cutoff (min sf si)
  let M := max Mh Mf
  have hs0 : 0 < s0 := lt_min c.cutoff_pos (lt_min hsf hsi)
  have hM : 1 < M := hMh.trans_le (le_max_left _ _)
  refine ⟨s0, M, E, hs0, hM, hE, physical_origin_branch_sign_norm hBi hbsq, ?_⟩
  intro s hs hss0 r Mi ki hr hMi
  have hsc : s ≤ c.cutoff := hss0.trans (min_le_left _ _)
  have hsf' : s ≤ sf := hss0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsi' : s ≤ si := hss0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht : Tendsto (fun l : ℕ => 2 * l + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    exact eventually_atTop.mpr ⟨n, fun l hl => by omega⟩
  have hrad : Tendsto (fun l : ℕ => r / (4 * ((2 * l + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (r / 4)).comp ht using 1
    ext l
    dsimp only [Function.comp_def]
    ring
  have hRmin : 0 < min c.radius R := lt_min c.radius_pos hR
  filter_upwards [hhigher, hfirst s hs hsf' r Mi ki,
    hrad.eventually (Iio_mem_nhds hRmin)] with l hh hf hradl
  intro d j hres hj hlog
  have hrc : r / (4 * ((2 * l + 1 : ℕ) : ℝ)) ≤ c.radius :=
    hradl.le.trans (min_le_left _ _)
  have hrR : r / (4 * ((2 * l + 1 : ℕ) : ℝ)) ≤ R := hradl.le.trans (min_le_right _ _)
  have hjh : Mh * ((2 * l + 1 : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)).trans hj
  have hjf : Mf * ((2 * l + 1 : ℕ) : ℝ) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right Mh Mf) (sq_nonneg (((2 * l + 1 : ℕ) : ℝ)))).trans hj
    exact h.trans (by exact_mod_cast Nat.le_succ j)
  have hhj := hh r s Mi ki d hs hsc hrc j hjh
  have hfj := hf d j hjf hlog
  have hid := hidentity (2 * l) (show Odd (2 * l + 1) from ⟨l, rfl⟩)
    r s Mi ki d hr hs.le hMi hsi' hrR hres j
  dsimp only at hfj ⊢
  rw [hid]
  calc
    _ ≤ ‖physicalWindingSectorCoefficient d j 1 + physicalWindingSectorCoefficient d j (-1) -
        (Complex.sqrt (B 0) / b 0) * _‖ +
        ∑ w ∈ higherWindingSectorIndices (2 * l), ‖physicalWindingSectorCoefficient d j w‖ :=
      winding_sum_error_le_first_pair (2 * l) (physicalWindingSectorCoefficient d j) _
    _ ≤ _ + _ := add_le_add hfj hhj
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
