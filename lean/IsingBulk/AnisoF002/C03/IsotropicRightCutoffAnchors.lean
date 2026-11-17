import IsingBulk.AnisoF002.C03.IsotropicRightCutoffProducts

/-!
# Named compact anchors for every cutoff jet

The upper return is placed in an actually excluded sine-bump plateau.
On the shifted one-sided fundamental interval, every nonzero jet of a
telescoped term has the same named compact left anchor.  A quantitative
cosine gap is retained for the subsequent physical root estimate.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators Classical

theorem rightCutoffAnchor_zero_on_plateau {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {N : ℕ} (a : Fin N) (θ : Fin N → ℝ) (hθ : θ a ∈ Icc (-b - δ / 2) ρ) :
    rightCutoffAnchor b δ ρ a θ = 0 := by
  simp only [rightCutoffAnchor, periodicRightCutoff_one h hθ, Complex.ofReal_one, sub_self, zero_mul]

theorem rightCutoffAnchor_tsupport {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {N : ℕ} (a : Fin N) :
    tsupport (rightCutoffAnchor b δ ρ a) ⊆
      {θ : Fin N → ℝ | θ a ≤ -b - δ / 2 ∨ ρ ≤ θ a} := by
  apply closure_minimal
  · intro θ hθ
    by_cases hl : θ a ≤ -b - δ / 2
    · exact Or.inl hl
    · right
      by_contra hu
      exact hθ (rightCutoffAnchor_zero_on_plateau h a θ
        ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩)
  · exact (isClosed_le (continuous_apply a) continuous_const).union
      (isClosed_le continuous_const (continuous_apply a))

theorem rightCutoffAnchor_jet_support {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {N : ℕ} (a : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hne : iteratedFDeriv ℝ k (rightCutoffAnchor b δ ρ a) θ ≠ 0) :
    θ a ≤ -b - δ / 2 ∨ ρ ≤ θ a :=
  rightCutoffAnchor_tsupport h a ((support_iteratedFDeriv_subset k) hne)

theorem upperPeriodicBump_one_on_plateau {η ρ θ : ℝ} (hη : 0 < η)
    (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2) (hgap : 2 * η ≤ Real.sin ρ)
    (hθ : θ ∈ Icc ρ (Real.pi - ρ)) : upperPeriodicBump η θ = 1 := by
  have hs : Real.sin ρ ≤ Real.sin θ := by
    by_cases ht : θ ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht hθ.1
    · calc
        _ ≤ Real.sin (Real.pi - θ) := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith) (by linarith [hθ.2])
        _ = _ := Real.sin_pi_sub θ
  exact upperPeriodicBump_one hη (hgap.trans hs)

theorem upper_plateau_excluded_of_small_population {η ρ : ℝ} {N : ℕ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin ρ) (θ : Fin N → ℝ)
    (hP : (∑ i, upperPeriodicBump η (θ i)) ≤ 1 / 2) (a : Fin N) :
    θ a ∉ Icc ρ (Real.pi - ρ) := by
  intro ha
  have hsum := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => (upperPeriodicBump_bounds η (θ i)).1)
    (Finset.mem_univ a)
  rw [upperPeriodicBump_one_on_plateau hη hρ hρπ hgap ha] at hsum
  linarith

theorem rightCutoffAnchor_jet_compact_left {b δ ρ η : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin ρ) {N : ℕ} (a : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hP : (∑ i, upperPeriodicBump η (θ i)) ≤ 1 / 2)
    (hθ : θ a ∈ Icc (-Real.pi - ρ) (Real.pi - ρ))
    (hne : iteratedFDeriv ℝ k (rightCutoffAnchor b δ ρ a) θ ≠ 0) :
    θ a ∈ Icc (-Real.pi - ρ) (-b - δ / 2) := by
  have hex := upper_plateau_excluded_of_small_population hη h.rho_pos hρπ hgap θ hP a
  refine ⟨hθ.1, ?_⟩
  rcases rightCutoffAnchor_jet_support h a k θ hne with hl | hu
  · exact hl
  · exact (hex ⟨hu, hθ.2⟩).elim

theorem rightCutoffAnchor_jet_two_compact_arcs {b δ ρ η : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin ρ) {N : ℕ} (a : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hP : (∑ i, upperPeriodicBump η (θ i)) ≤ 1 / 2)
    (hθ : θ a ∈ Icc (-Real.pi) Real.pi)
    (hne : iteratedFDeriv ℝ k (rightCutoffAnchor b δ ρ a) θ ≠ 0) :
    θ a ∈ Icc (-Real.pi) (-b - δ / 2) ∪ Icc (Real.pi - ρ) Real.pi := by
  have hex := upper_plateau_excluded_of_small_population hη h.rho_pos hρπ hgap θ hP a
  rcases rightCutoffAnchor_jet_support h a k θ hne with hl | hu
  · exact Or.inl ⟨hθ.1, hl⟩
  · right
    refine ⟨?_, hθ.2⟩
    by_contra hh
    exact hex ⟨hu, (lt_of_not_ge hh).le⟩

theorem compact_left_anchor_cosine_gap {b δ ρ θ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hρ : 0 ≤ ρ) (hgap : b + δ / 2 + ρ < Real.pi)
    (hθ : θ ∈ Icc (-Real.pi - ρ) (-b - δ / 2)) :
    0 < Real.cos b - Real.cos (b + δ / 2) ∧
      Real.cos θ ≤ Real.cos b - (Real.cos b - Real.cos (b + δ / 2)) := by
  have hR : 0 ≤ b + δ / 2 := by positivity
  have hRπ : b + δ / 2 ≤ Real.pi := by linarith
  have hstrict := Real.cos_lt_cos_of_nonneg_of_le_pi hb.le hRπ (by linarith)
  refine ⟨sub_pos.mpr hstrict, ?_⟩
  have hθneg : θ ≤ 0 := by linarith [hθ.2]
  have hlo : b + δ / 2 ≤ |θ| := by rw [abs_of_nonpos hθneg]; linarith [hθ.2]
  have hhi : |θ| ≤ 2 * Real.pi - (b + δ / 2) := by rw [abs_of_nonpos hθneg]; linarith [hθ.1]
  have hc := cos_le_cos_of_outside_arc hR hlo hhi
  linarith

theorem exists_right_cutoff_buffers {b : ℝ} (hb : 0 < b) (hbπ : b < Real.pi) :
    ∃ ρ δ0 η0 : ℝ, 0 < ρ ∧ 0 < δ0 ∧ 0 < η0 ∧ 3 * ρ < Real.pi ∧ 2 * ρ < b ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ δ0 → RightCutoffGeometry b δ ρ ∧
        δ ≤ 2 * ρ ∧ b + δ / 2 + ρ < Real.pi) ∧
      ∀ η : ℝ, 0 < η → η ≤ η0 → 2 * η < Real.sin ρ ∧ 4 * η ≤ Real.sin b := by
  let ρ := min (b / 8) ((Real.pi - b) / 8)
  have hρ : 0 < ρ := lt_min (by positivity) (by linarith)
  have hρb : ρ ≤ b / 8 := min_le_left _ _
  have hρp : ρ ≤ (Real.pi - b) / 8 := min_le_right _ _
  have hρπ : ρ < Real.pi := by linarith [Real.pi_pos]
  have hsinρ := Real.sin_pos_of_pos_of_lt_pi hρ hρπ
  have hsinb := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  let η0 := min (Real.sin ρ / 4) (Real.sin b / 4)
  have hη0 : 0 < η0 := lt_min (by positivity) (by positivity)
  refine ⟨ρ, ρ, η0, hρ, hρ, hη0, by linarith, by linarith, ?_, ?_⟩
  · intro δ hδ hδρ
    refine ⟨⟨hb, hδ, hρ, by linarith, by linarith⟩, by linarith, by linarith⟩
  · intro η _ hη
    have hηρ := hη.trans (min_le_left _ _)
    have hηb := hη.trans (min_le_right _ _)
    constructor <;> linarith

end
end IsingBulk.AnisoF002.Isotropic
