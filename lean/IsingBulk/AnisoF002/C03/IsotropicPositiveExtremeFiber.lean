import IsingBulk.AnisoF002.C03.IsotropicConstrainedPhasePath

/-!
# The actual positive extreme-coordinate fiber is one interval

All extrema, shell and rectangle conditions are retained on the genuine
constraint-preserving angular line. The resulting set is convex and
compact. This gives a single interval for the subsequent coarea change
of variable, with no disconnected-fiber counting assumption.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem constrainedAngleLine_convex_combination {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N)
    (t u a c : ℝ) (hac : a + c = 1) (k : Fin N) :
    constrainedAngleLine θ i j (a * t + c * u) k =
      a * constrainedAngleLine θ i j t k + c * constrainedAngleLine θ i j u k := by
  simp only [constrainedAngleLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(θ k) * hac

def positiveExtremeFiber {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b δ r : ℝ) : Set ℝ :=
  {t | (∀ k, constrainedAngleLine θ i j t k ∈ Icc (-b) δ) ∧
    (∀ k, constrainedAngleLine θ i j t i ≤ constrainedAngleLine θ i j t k) ∧
    (∀ k, constrainedAngleLine θ i j t k ≤ constrainedAngleLine θ i j t j) ∧
    r ≤ constrainedAngleLine θ i j t j - constrainedAngleLine θ i j t i ∧
    constrainedAngleLine θ i j t j - constrainedAngleLine θ i j t i ≤ 2 * r}

theorem positiveExtremeFiber_convex {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b δ r : ℝ) :
    Convex ℝ (positiveExtremeFiber θ i j b δ r) := by
  intro t ht u hu a c ha hc hac
  change a + c = 1 at hac
  have he := constrainedAngleLine_convex_combination θ i j t u a c hac
  change a • t + c • u ∈ positiveExtremeFiber θ i j b δ r
  simp only [smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [he k]
    constructor
    · have hh := add_le_add (mul_le_mul_of_nonneg_left (ht.1 k).1 ha)
        (mul_le_mul_of_nonneg_left (hu.1 k).1 hc)
      have hh' : a * (-b) + c * (-b) = -b := by linear_combination (-b) * hac
      rwa [hh'] at hh
    · have hh := add_le_add (mul_le_mul_of_nonneg_left (ht.1 k).2 ha)
        (mul_le_mul_of_nonneg_left (hu.1 k).2 hc)
      have hh' : a * δ + c * δ = δ := by linear_combination δ * hac
      rwa [hh'] at hh
  · intro k
    rw [he i, he k]
    exact add_le_add (mul_le_mul_of_nonneg_left (ht.2.1 k) ha)
      (mul_le_mul_of_nonneg_left (hu.2.1 k) hc)
  · intro k
    rw [he k, he j]
    exact add_le_add (mul_le_mul_of_nonneg_left (ht.2.2.1 k) ha)
      (mul_le_mul_of_nonneg_left (hu.2.2.1 k) hc)
  · rw [he j, he i]
    have hh := add_le_add (mul_le_mul_of_nonneg_left ht.2.2.2.1 ha)
      (mul_le_mul_of_nonneg_left hu.2.2.2.1 hc)
    have hh' : a * r + c * r = r := by linear_combination r * hac
    rw [hh'] at hh
    linarith only [hh]
  · rw [he j, he i]
    have hh := add_le_add (mul_le_mul_of_nonneg_left ht.2.2.2.2 ha)
      (mul_le_mul_of_nonneg_left hu.2.2.2.2 hc)
    have hh' : a * (2 * r) + c * (2 * r) = 2 * r := by linear_combination (2 * r) * hac
    rw [hh'] at hh
    linarith only [hh]

theorem positiveExtremeFiber_isClosed {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b δ r : ℝ) :
    IsClosed (positiveExtremeFiber θ i j b δ r) := by
  have hk (k : Fin N) : Continuous (fun t : ℝ => constrainedAngleLine θ i j t k) := by
    unfold constrainedAngleLine
    fun_prop
  unfold positiveExtremeFiber
  simp only [mem_Icc, ofPred_and, ofPred_forall]
  exact (isClosed_iInter (fun k => (isClosed_le continuous_const (hk k)).inter
      (isClosed_le (hk k) continuous_const))).inter
    ((isClosed_iInter (fun k => isClosed_le (hk i) (hk k))).inter
      ((isClosed_iInter (fun k => isClosed_le (hk k) (hk j))).inter
        ((isClosed_le continuous_const ((hk j).sub (hk i))).inter
          (isClosed_le ((hk j).sub (hk i)) continuous_const))))

theorem positiveExtremeFiber_isCompact {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N)
    (hij : i ≠ j) (b δ r : ℝ) : IsCompact (positiveExtremeFiber θ i j b δ r) := by
  apply isCompact_Icc.of_isClosed_subset (positiveExtremeFiber_isClosed θ i j b δ r)
    (s := Icc (-b - θ i) (δ - θ i))
  intro t ht
  have hh := ht.1 i
  rw [constrainedAngleLine_first θ i j hij t] at hh
  exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩

theorem positiveExtremeFiber_ordConnected {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b δ r : ℝ) :
    OrdConnected (positiveExtremeFiber θ i j b δ r) :=
  (positiveExtremeFiber_convex θ i j b δ r).ordConnected

theorem positiveExtremeFiber_eq_interval {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N)
    (hij : i ≠ j) (b δ r : ℝ) (hne : (positiveExtremeFiber θ i j b δ r).Nonempty) :
    ∃ a c : ℝ, a ≤ c ∧ positiveExtremeFiber θ i j b δ r = Icc a c := by
  have hK := positiveExtremeFiber_isCompact θ i j hij b δ r
  obtain ⟨a, ha⟩ := hK.exists_isLeast hne
  obtain ⟨c, hc⟩ := hK.exists_isGreatest hne
  refine ⟨a, c, ha.2 hc.1, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨ha.2 hx, hc.2 hx⟩
  · exact (positiveExtremeFiber_ordConnected θ i j b δ r).out ha.1 hc.1

end IsingBulk.AnisoF002.Isotropic
