import IsingBulk.Joint.RegularEdges.FamilyTailJets
import IsingBulk.Joint.Negative.CompactAnalyticBounds

/-! # All complete family coefficient tails with a nonconstant physical prefactor -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Joint.FormFactors
  IsingBulk.Joint.Negative Set Filter Metric
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_prefactored_family_coefficient_tails {b : ℝ} (B S A : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hBa : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hSa : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hAa : ∀eta∈Q,AnalyticAt ℂ A (0,eta))
    (hB : ∀eta∈Q,0<(B (0,eta)).im) (hS : ∀eta∈Q,S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → ∀k : ℕ,
      ‖iteratedDeriv j (fun t=>A (t,eta)*angularCoefficient (2*j+3+k) b
        (fun v=>B (v,eta)) (fun v=>S (v,eta)) t) u‖≤G k := by
  obtain ⟨ρ,hρ,htube⟩ := compact_admissible_family_tube B S hQ hBa hSa hB hS
  obtain ⟨δ,hδ,hjets⟩ := compact_family_full_coefficient_tails B S hb hQ hBa hSa hB hS
  choose M hM hM0 hMb using hjets
  obtain ⟨r,C,hr,hC,hAb⟩ := compact_analytic_uniform_bound A hQ hAa
  refine ⟨min ρ (min δ (r/2)),lt_min hρ (lt_min hδ (half_pos hr)),?_⟩
  intro j
  let J : ℕ→ℝ := fun i=>C/(r/(2*((i+1:ℕ):ℝ)))^i
  have hJ (i : ℕ) : 0≤J i := by dsimp [J]; positivity
  let D := ∑i∈Finset.range (j+1),J i
  have hD : 0≤D := Finset.sum_nonneg (fun i _=>hJ i)
  let W : ℕ→ℝ := fun k=>∑i∈Finset.range (j+1),M i (2*(j-i)+k)
  have hW (k : ℕ) : 0≤W k := Finset.sum_nonneg (fun i _=>hM0 i _)
  have hWs : Summable W := by
    apply summable_sum
    intro i _
    exact (hM i).comp_injective (i := fun k : ℕ=>2*(j-i)+k) (by intro x y h; dsimp at h; omega)
  refine ⟨fun k=>2^j*D*W k,hWs.mul_left _,fun k=>mul_nonneg (by positivity) (hW k),?_⟩
  intro eta heta u hu hi k
  have huρ := hu.trans_le (min_le_left _ _)
  have huδ := (hu.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hur := (hu.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hAu : AnalyticOnNhd ℂ (fun t=>A (t,eta)) (ball 0 r) := by
    intro t ht
    exact (hAb eta heta t (by simpa using ht)).1.comp
      (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hAjet (i : ℕ) (hij : i≤j) : ‖iteratedFDeriv ℂ i (fun t=>A (t,eta)) u‖≤D := by
    have hh := norm_iteratedFDeriv_le_on_half_ball i hr hC.le hAu
      (fun t ht=>(hAb eta heta t (by simpa using ht)).2.le) (by simpa using hur)
    exact hh.trans (Finset.single_le_sum (fun a (_ : a∈Finset.range (j+1))=>hJ a)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega)))
  have hCjet (i : ℕ) (hij : i≤j) :
      ‖iteratedFDeriv ℂ i (angularCoefficient (2*j+3+k) b (fun t=>B (t,eta)) (fun t=>S (t,eta))) u‖≤W k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hh := hMb i eta heta u huδ hi (2*(j-i)+k)
    rw [show 2*i+3+(2*(j-i)+k)=2*j+3+k by omega] at hh
    exact hh.trans (Finset.single_le_sum (f:=fun a=>M a (2*(j-a)+k))
      (fun a (_ : a∈Finset.range (j+1))=>hM0 a _)
      (show i∈Finset.range (j+1) from Finset.mem_range.mpr (by omega)))
  have hp : (u,(B (u,eta),S (u,eta)))∈independentUpperDomain := ⟨hi,(htube eta heta u huρ.le).2.2⟩
  have htrace : AnalyticAt ℂ (fun t=>(t,(B (t,eta),S (t,eta)))) u :=
    analyticAt_id.prod (((htube eta heta u huρ.le).1.comp
      (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)).prod
      ((htube eta heta u huρ.le).2.1.comp
        (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)))
  have hcoef : ContDiffAt ℂ j (angularCoefficient (2*j+3+k) b (fun t=>B (t,eta)) (fun t=>S (t,eta))) u := by
    have hh : ContDiffAt ℂ j (independentAngularCoefficient (2*j+3+k) b ∘
        (fun t=>(t,(B (t,eta),S (t,eta))))) u :=
      (independentAngularCoefficient_contDiffAt _ j hp).comp u htrace.contDiffAt
    exact hh
  have hAc : ContDiffAt ℂ j (fun t=>A (t,eta)) u :=
    (hAu u (by simpa using hur.trans (half_lt_self hr))).contDiffAt
  have hh := contDiffAt_product_uniform_jets j j le_rfl hAc hcoef hD (hW k) hAjet hCjet
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  exact hh

end
end IsingBulk.Joint.RegularEdges
