import IsingBulk.Anisotropic.RegularEdges.NumeratorJets
import IsingBulk.Anisotropic.RegularEdges.MatchedSummability

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

def particleEdgeMajorant (r C M : ℝ) (N : ℕ) : ℝ :=
  if N%2=0 then evenEdgeMajorant r C M (N/2) else oddEdgeMajorant r C M (N/2)

@[simp] theorem particleEdgeMajorant_even (r C M : ℝ) (n : ℕ) :
    particleEdgeMajorant r C M (2*n)=evenEdgeMajorant r C M n := by
  simp [particleEdgeMajorant]

@[simp] theorem particleEdgeMajorant_odd (r C M : ℝ) (n : ℕ) :
    particleEdgeMajorant r C M (2*n+1)=oddEdgeMajorant r C M n := by
  simp [particleEdgeMajorant, Nat.add_div]

 theorem particleEdgeMajorant_nonneg {r C M : ℝ} (hr : 0≤r) (hC : 0≤C) (hM : 0≤M) (N : ℕ) :
    0≤particleEdgeMajorant r C M N := by
  unfold particleEdgeMajorant evenEdgeMajorant oddEdgeMajorant
  split <;> positivity

 theorem edgeNumerator_all_jets {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M K : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ u : ℂ, ‖u‖<δ → ∀ (N : ℕ) (q : Fin N → ℝ),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      AnalyticAt ℂ (fun v => edgeNumerator b B S v (List.ofFn q)) u ∧
      ∀ k≤j, ‖iteratedDeriv k (fun v => edgeNumerator b B S v (List.ofFn q)) u‖≤
        K*particleEdgeMajorant r C M N := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hj⟩ := edgeNumerator_uniform_derivatives hb hB hc hS hS0
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    (edgeNumerator_eventually_analyticAt hb hB hc hS hS0)
  let K : ℝ := 1+∑ k ∈ Finset.range (j+1), (k.factorial:ℝ)/δ^k
  have hterm (k : ℕ) : 0≤(k.factorial:ℝ)/δ^k := by positivity
  have hK : 0<K := by
    have hh := Finset.sum_nonneg (fun k (_ : k∈Finset.range (j+1)) => hterm k)
    dsimp [K]
    linarith
  refine ⟨min δ η,r,C,M,K,lt_min hδ hη,hr,hr1,hC,hM,hK,?_⟩
  intro u hu N q hq
  have hqs : ∀ a∈List.ofFn q, a∈Icc (-Real.pi) Real.pi := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hq i
  refine ⟨hηball (show u∈ball (0:ℂ) η by simpa using hu.trans_le (min_le_right _ _)) _ hqs,?_⟩
  intro k hk
  have hbound : ‖iteratedDeriv k (fun v => edgeNumerator b B S v (List.ofFn q)) u‖≤
      (k.factorial:ℝ)*particleEdgeMajorant r C M N/δ^k := by
    have hh := hj k u (hu.trans_le (min_le_left _ _))
    by_cases hp : N%2=0
    · simpa only [particleEdgeMajorant,ite_eq_left hp] using
        hh.1 (N/2) (List.ofFn q) (by simp only [List.length_ofFn]; omega) hqs
    · simpa only [particleEdgeMajorant,ite_eq_right hp] using
        hh.2 (N/2) (List.ofFn q) (by simp only [List.length_ofFn]; omega) hqs
  have hle : (k.factorial:ℝ)/δ^k≤K := by
    have hh := Finset.single_le_sum (fun i (_ : i∈Finset.range (j+1)) => hterm i)
      (show k∈Finset.range (j+1) from Finset.mem_range.mpr (by omega))
    dsimp [K]
    linarith
  exact hbound.trans (by
    convert mul_le_mul_of_nonneg_right hle (particleEdgeMajorant_nonneg hr.le hC.le hM.le N) using 1; ring)

end IsingBulk.Anisotropic.RegularEdges
