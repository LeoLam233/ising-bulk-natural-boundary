import IsingBulk.AnisoF002.C03.PhysicalContourGeometry
import IsingBulk.AnisoF002.RegularTail.CanceledPair
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Joint holomorphy and a uniform kernel bound for the original full density

All coordinates and the physical parameter vary jointly.  Pole exclusions
come from the independently constructed literal annulus; no finite contour
holomorphy or susceptibility theorem from the historical route is used.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.First
open scoped Topology BigOperators

theorem literal_coordinateProduct_norm_lt_one {N : ℕ} (hN : 0 < N)
    {x : Fin N → ℂ} (hx : ∀ i, ‖x i‖ < 1) : ‖coordinateProduct x‖ < 1 := by
  cases N with
  | zero => omega
  | succ n =>
    rw [coordinateProduct, Fin.prod_univ_succ, norm_mul]
    have ht : ‖∏ i : Fin n, x i.succ‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => (hx i.succ).le)
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_lt (by simpa using hx 0)

theorem literal_coordinateProduct_denominator {N : ℕ} (hN : 0 < N)
    {x : Fin N → ℂ} (hx : ∀ i, ‖x i‖ < 1) : 1 - coordinateProduct x ≠ 0 := by
  intro he
  have hh := literal_coordinateProduct_norm_lt_one hN hx
  rw [← sub_eq_zero.mp he, norm_one] at hh
  exact (lt_irrefl _) hh

theorem literal_pairProduct_analyticAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    {x : E → Fin N → ℂ} {p : E}
    (hx : ∀ i, AnalyticAt ℂ (fun q => x q i) p)
    (hn : ∀ i j, 1 - x p i * x p j ≠ 0) :
    AnalyticAt ℂ (fun q => First.pairProduct (x q)) p := by
  unfold First.pairProduct First.pairKernel
  exact Finset.univ.analyticAt_fun_prod (fun i _ =>
    (Finset.univ.filter (fun j => i < j)).analyticAt_fun_prod (fun j _ =>
      ((hx i).sub (hx j)).div (analyticAt_const.sub ((hx i).mul (hx j))) (hn i j)))

theorem literal_fullDensity_joint_analyticAt {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} {x y : Fin N → ℂ} (h : ContourAnnulus lam z r)
    (hx : ∀ i, r ≤ ‖x i‖ ∧ ‖x i‖ < 1) (hy : ∀ i, r ≤ ‖y i‖ ∧ ‖y i‖ < 1) :
    AnalyticAt ℂ (fun p : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) =>
      fullDensity lam p.1 p.2.1 p.2.2) (z, x, y) := by
  let p := (z, x, y)
  have dz : AnalyticAt ℂ (fun q : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => q.1) p :=
    analyticAt_fst
  have dx (i : Fin N) : AnalyticAt ℂ
      (fun q : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => q.2.1 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp
      (analyticAt_fst.comp analyticAt_snd)
  have dy (i : Fin N) : AnalyticAt ℂ
      (fun q : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => q.2.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp
      (analyticAt_snd.comp analyticAt_snd)
  have hx0 (i) : x i ≠ 0 := norm_pos_iff.mp (h.1.trans_le (hx i).1)
  have hy0 (i) : y i ≠ 0 := norm_pos_iff.mp (h.1.trans_le (hy i).1)
  have dX := Finset.univ.analyticAt_fun_prod (fun i _ => dx i)
  have dY := Finset.univ.analyticAt_fun_prod (fun i _ => dy i)
  have dPX := literal_pairProduct_analyticAt dx (fun i j =>
    pair_root_denominator_ne_zero (hx i).2 (hx j).2)
  have dPY := literal_pairProduct_analyticAt dy (fun i j =>
    pair_root_denominator_ne_zero (hy i).2 (hy j).2)
  have dD : AnalyticAt ℂ (fun q : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) =>
      ∏ i, (sliceDispersion lam q.1 (q.2.1 i) (q.2.2 i))⁻¹) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply AnalyticAt.inv
    · unfold sliceDispersion dispersionPolynomial spectralA spectralS spectralT
      exact (((Complex.analyticAt_cosh.comp dz).mul
        (Complex.analyticAt_cosh.comp (analyticAt_const.mul dz))).sub
        (((Complex.analyticAt_sinh.comp dz).div_const).mul ((dx i).add ((dx i).inv (hx0 i))))).sub
        (((Complex.analyticAt_sinh.comp (analyticAt_const.mul dz)).div_const).mul
          ((dy i).add ((dy i).inv (hy0 i))))
    · exact h.2.2 _ _ (hx i).1 (hx i).2.le (hy i).1 (hy i).2.le
  have dnum := ((analyticAt_const (v := (1 : ℂ))).add dX).mul
    ((analyticAt_const (v := (1 : ℂ))).add dY)
  have dden := ((dX.mul dY).mul ((analyticAt_const (v := (1 : ℂ))).sub dX)).mul
    ((analyticAt_const (v := (1 : ℂ))).sub dY)
  have hn : coordinateProduct x * coordinateProduct y * (1 - coordinateProduct x) *
      (1 - coordinateProduct y) ≠ 0 := mul_ne_zero (mul_ne_zero
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)))
    (literal_coordinateProduct_denominator hN (fun i => (hx i).2)))
    (literal_coordinateProduct_denominator hN (fun i => (hy i).2))
  exact (dnum.div dden hn).mul ((dPX.mul dPY).mul dD)

theorem literal_local_inverse_dispersion_bound {lam r : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ w in 𝓝 z, ∀ x y : ℂ, ‖x‖ = r → ‖y‖ = r →
      ‖(sliceDispersion lam w x y)⁻¹‖ ≤ M := by
  let K : Set (ℂ × ℂ) := sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hp (p : ℂ × ℂ) (hp : p ∈ K) :
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ sliceDispersion lam z p.1 p.2 ≠ 0 := by
    have hx : ‖p.1‖ = r := by simpa using hp.1
    have hy : ‖p.2‖ = r := by simpa using hp.2
    exact ⟨norm_ne_zero_iff.mp (hx.trans_ne h.1.ne'), norm_ne_zero_iff.mp (hy.trans_ne h.1.ne'),
      h.2.2 _ _ hx.ge (hx.le.trans h.2.1.le) hy.ge (hy.le.trans h.2.1.le)⟩
  have hc : ContinuousOn (fun p : ℂ × ℂ => (sliceDispersion lam z p.1 p.2)⁻¹) K := by
    intro p hpk
    have hh := hp p hpk
    exact (((literal_sliceDispersion_continuousAt hh.1 hh.2.1).inv₀ hh.2.2).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  let L := max M 0 + 1
  have hL : 0 < L := by dsimp [L]; linarith [le_max_right M 0]
  refine ⟨L, hL, ?_⟩
  have he : ∀ᶠ w in 𝓝 z, ∀ p ∈ K, ‖(sliceDispersion lam w p.1 p.2)⁻¹‖ < L := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hpk
    have hh := hp p hpk
    apply (((literal_sliceDispersion_continuousAt hh.1 hh.2.1).inv₀ hh.2.2).norm).eventually_lt
      continuousAt_const
    exact (hM p hpk).trans_lt (by dsimp [L]; linarith [le_max_left M 0])
  filter_upwards [he] with w hw
  intro x y hx hy
  exact (hw (x, y) ⟨by simpa using hx, by simpa using hy⟩).le

end
end IsingBulk.AnisoF002.RegularTail.C03
