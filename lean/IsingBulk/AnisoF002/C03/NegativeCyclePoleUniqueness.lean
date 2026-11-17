import IsingBulk.AnisoF002.C03.NegativeInnerMeasurableRemainder
import IsingBulk.AnisoF002.C03.NegativePhysicalAngularError

/-!
# Uniqueness and signed-lift identification of the actual cycle pole

One fixed temperature disk and angular cutoff work before the particle
number.  The phase factor has no zero there, so the pole selected through
unsigned angles equals the pole in every cosine-equivalent signed lift,
including the actual first-winding pole used in the full residue estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def ActualPhaseUniqueOn (B : ℂ → ℂ) (φ R s : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ q : Fin n → ℝ, angularShortSquare q ≤ s →
    ∀ t u : ℂ, ‖t‖ ≤ R → ‖u‖ ≤ R →
      realPhaseTotal B φ n q t = (n : ℂ) * ((φ : ℂ) * Complex.I) →
      realPhaseTotal B φ n q u = (n : ℂ) * ((φ : ℂ) * Complex.I) → t = u

theorem InnerPoleData.phase_zero_unique {B : ℂ → ℂ} {φ R s C : ℝ} {a : ℂ} {n : ℕ}
    (d : InnerPoleData B φ n R s C a) (hn : 0 < n)
    (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s)
    {t : ℂ} (ht : ‖t‖ ≤ R)
    (hphase : realPhaseTotal B φ n q t = (n : ℂ) * ((φ : ℂ) * Complex.I)) :
    t = d.pole q := by
  have hmem : t ∈ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  have he := d.phase_factor q hq t hmem
  rw [hphase] at he
  have hz : (n : ℂ) * (t - d.pole q) *
      dslope (realPhaseAverage B φ n q) (d.pole q) t = 0 := by
    exact add_left_cancel (a := (n : ℂ) * ((φ : ℂ) * Complex.I)) (by simpa using he.symm)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfac := (d.factor_bounds q hq t hmem).2.2
  exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hfac)).resolve_left hn0)

theorem exists_actual_phase_unique_ball {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ R s : ℝ, 0 < R ∧ 0 < s ∧ ActualPhaseUniqueOn B φ R s := by
  obtain ⟨R, s, C, a, hR, hs, _, _, _, hd⟩ := exists_actual_inner_pole_data hB hφ hπ hBi
  refine ⟨R, s, hR, hs, ?_⟩
  intro n hn q hq t u ht hu hpt hpu
  obtain ⟨d⟩ := hd n hn
  exact (d.phase_zero_unique hn q hq ht hpt).trans (d.phase_zero_unique hn q hq hu hpu).symm

theorem negativeGlobalPhase_cos_congr (B : ℂ → ℂ) (φ : ℝ) (t : ℂ)
    {x y : ℂ} (hxy : Complex.cos x = Complex.cos y) :
    negativeGlobalPhase B φ (t, x) = negativeGlobalPhase B φ (t, y) := by
  simp only [negativeGlobalPhase, localNegativeDispersion, hxy]

theorem realPhaseTotal_cos_congr (B : ℂ → ℂ) (φ : ℝ) {n : ℕ}
    {q q' : Fin n → ℝ} (hcos : ∀ i, Real.cos (q i) = Real.cos (q' i)) :
    realPhaseTotal B φ n q = realPhaseTotal B φ n q' := by
  funext t
  apply Finset.sum_congr rfl
  intro i _
  apply negativeGlobalPhase_cos_congr
  simpa only [Complex.ofReal_cos] using congrArg (fun x : ℝ => (x : ℂ)) (hcos i)

theorem InnerRemainderFamily.pole_phase {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ n r s M kappa) (hn : 0 < n)
    (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s) :
    realPhaseTotal B φ n q (d.pole q) = (n : ℂ) * ((φ : ℂ) * Complex.I) := by
  rw [realPhaseTotal_eq_average B φ hn q, d.pole_zero ⟨q, hq⟩, mul_zero, add_zero]

theorem InnerRemainderFamily.pole_eq_of_phase {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ n r s M kappa) (hn : 0 < n)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n : ℝ)) ≤ R)
    (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s) (hq0 : angularShortSquare q ≤ s0)
    {t : ℂ} (ht : ‖t‖ ≤ R)
    (hp : realPhaseTotal B φ n q t = (n : ℂ) * ((φ : ℂ) * Complex.I)) :
    d.pole q = t :=
  hu n hn q hq0 _ _ ((d.pole_bound ⟨q, hq⟩).trans hR) ht (d.pole_phase hn q hq) hp

theorem InnerRemainderFamily.pole_cos_equivariant {b B : ℂ → ℂ}
    {φ r s M kappa R s0 : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ n r s M kappa) (hn : 0 < n)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n : ℝ)) ≤ R)
    (q q' : Fin n → ℝ) (hq : angularShortSquare q ≤ s) (hq' : angularShortSquare q' ≤ s)
    (hq0 : angularShortSquare q ≤ s0) (hcos : ∀ i, Real.cos (q i) = Real.cos (q' i)) :
    d.pole q = d.pole q' := by
  apply d.pole_eq_of_phase hn hu hR q hq hq0 ((d.pole_bound ⟨q', hq'⟩).trans hR)
  rw [realPhaseTotal_cos_congr B φ hcos]
  exact d.pole_phase hn q' hq'

theorem InnerRemainderFamily.pole_eq_first_winding {b B : ℂ → ℂ}
    {φ r s M kappa R s0 σ C Kρ Kp : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ n r s M kappa)
    (p : PhysicalFirstWindingData b B φ n σ C Kρ Kp) (hn : 0 < n)
    (hu : ActualPhaseUniqueOn B φ R s0) (hR : r / (4 * (n : ℝ)) ≤ R)
    (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s) (hq0 : angularShortSquare q ≤ s0)
    (v : zeroSumDisplacements n) (hv : displacementSquare n v < σ ^ 2)
    (hp : ‖p.pole v‖ ≤ R)
    (hcos : ∀ i, Complex.cos (q i : ℂ) =
      Complex.cos (((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) :
    d.pole q = p.pole v := by
  apply d.pole_eq_of_phase hn hu hR q hq hq0 hp
  rw [← p.phase v hv]
  exact Finset.sum_congr rfl (fun i _ => negativeGlobalPhase_cos_congr B φ _ (hcos i))

end
end IsingBulk.AnisoF002.NegativeHT
