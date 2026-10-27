import IsingBulk.Preferred22.FirstLocalAsymptotic
import IsingBulk.Preferred22.FirstLocalization
import IsingBulk.Preferred22.NonCancellation
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! A concrete smooth shape cutoff and the exact remaining finite-chart
remainder. The local source asymptotic is proved, so only the stated actual
complete-coefficient remainder bound remains in the assembly theorem. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology ContDiff

def preferredShapeCutoff {n : ℕ} (R : ℝ) (x : IsingBulk.First.ShapeSpace n) : ℂ :=
  (Real.smoothTransition (2-4*‖x‖^2/R^2):ℂ)

theorem preferredShapeCutoff_smooth {n : ℕ} (R : ℝ) :
    ContDiff ℝ ∞ (preferredShapeCutoff (n := n) R) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply Real.smoothTransition.contDiff.comp
  have hn : ContDiff ℝ ∞ (fun x : IsingBulk.First.ShapeSpace n => ‖x‖^2) := contDiff_norm_sq ℝ
  exact contDiff_const.sub ((contDiff_const.mul hn).div_const (R^2))

theorem preferredShapeCutoff_zero {n : ℕ} (R : ℝ) :
    preferredShapeCutoff (n := n) R 0=1 := by
  simp only [preferredShapeCutoff,norm_zero,zero_pow (by omega : 2≠0),mul_zero,zero_div,sub_zero]
  norm_num [Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2)]

theorem preferredShapeCutoff_bound {n : ℕ} (R : ℝ) (x : IsingBulk.First.ShapeSpace n) :
    ‖preferredShapeCutoff R x‖≤1 := by
  rw [preferredShapeCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem preferredShapeCutoff_support {n : ℕ} {R : ℝ} (hR : 0<R)
    (x : IsingBulk.First.ShapeSpace n) (hx : preferredShapeCutoff R x≠0) : ‖x‖<R := by
  have ha : 0<2-4*‖x‖^2/R^2 := by
    by_contra ha
    apply hx
    rw [preferredShapeCutoff,Real.smoothTransition.zero_of_nonpos (le_of_not_gt ha)]
    simp
  have hdiv : 4*‖x‖^2/R^2<2 := by linarith
  have hs := (div_lt_iff₀ (sq_pos_of_pos hR)).mp hdiv
  nlinarith [norm_nonneg x,sq_nonneg (‖x‖-R)]

theorem preferredShapeCutoff_one_near_zero {n : ℕ} {R : ℝ} (hR : 0<R)
    {x : IsingBulk.First.ShapeSpace n} (hx : ‖x‖≤R/2) : preferredShapeCutoff R x=1 := by
  have hd : 4*‖x‖^2/R^2≤1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [norm_nonneg x]
  rw [preferredShapeCutoff,Real.smoothTransition.one_of_one_le (by linarith)]
  simp

/-- Exact residual from Lemma 10.1 at the first order, with the reflected
multiplicity two and the literal physical localized integral. This records
an unproved bound; it does not add an axiom or assume a complete tail. -/
def PreferredFirstRemainderBound (α : ℝ) (n k : ℕ)
    (chi : IsingBulk.First.ShapeSpace n → ℂ) : Prop :=
  ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
    ‖iteratedDeriv k (coefficient (n+1)) ((1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I))-
      2*iteratedDeriv k (localizedPhysicalIntegral α chi)
        ((1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I))‖≤C

theorem preferred_local_asymptotic_limit {f : ℝ → ℂ} {Λ : ℂ}
    (h : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun ε => f ε-(Real.sqrt ε:ℂ)⁻¹*Λ) (fun ε => (Real.sqrt ε:ℂ)⁻¹)) :
    Tendsto (fun ε : ℝ => Real.sqrt ε • f ε) (𝓝[>] 0) (𝓝 Λ) := by
  have hl := h.tendsto_div_nhds_zero.add (tendsto_const_nhds (x := Λ))
  simp only [zero_add] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hs : (Real.sqrt ε:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show 0<ε from hε)).ne'
  rw [Complex.real_smul]
  field_simp
  ring

/-- The nonzero first coefficient follows from the already-proved actual
local source asymptotic and precisely the bounded complete remainder. -/
theorem preferred_first_singularity_of_bounded_remainder {n : ℕ} (hn : 1≤n)
    (he : Even (n+1)) (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2)
    (ha : Complex.exp (-(n+1:ℂ)*(α:ℂ)*Complex.I)=1) :
    ∃ R : ℝ,0<R ∧ ∀ ρ : ℝ,0<ρ → ρ≤R →
      PreferredFirstRemainderBound α n ((n+1)^2/2-1) (preferredShapeCutoff ρ) →
      PreferredFirstSingularityStatement (Complex.exp ((α:ℂ)*Complex.I))
        (n+1) ((n+1)^2/2-1) := by
  obtain ⟨hΛ,R,hR,hasym⟩ := localizedPhysical_source_asymptotic hn he α hα hαπ ha
  refine ⟨R,hR,?_⟩
  intro ρ hρ hρR hrem
  let k := (n+1)^2/2-1
  let Λ := IsingBulk.First.localLeadingCoefficient (equalAngleData α hα hαπ) n k
  let path := fun ε : ℝ => (1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I)
  let f := fun ε : ℝ => iteratedDeriv k
    (localizedPhysicalIntegral α (preferredShapeCutoff (n := n) ρ)) (path ε)
  let g := fun ε : ℝ => iteratedDeriv k (coefficient (n+1)) (path ε)-2*f ε
  have hf : Tendsto (fun ε : ℝ => Real.sqrt ε • f ε) (𝓝[>] 0) (𝓝 Λ) := by
    apply preferred_local_asymptotic_limit
    exact hasym (preferredShapeCutoff ρ) (preferredShapeCutoff_smooth ρ).continuous
      (preferredShapeCutoff_zero ρ) (preferredShapeCutoff_bound ρ)
      (fun x hx => (preferredShapeCutoff_support hρ x hx).trans_le hρR)
  obtain ⟨C,ε₀,_hC,hε₀,hbound⟩ := hrem
  have hg : Tendsto (fun ε : ℝ => Real.sqrt ε • g ε) (𝓝[>] 0) (𝓝 0) := by
    apply sqrt_log_bound_tendsto_zero (C := C) (D := 0) hε₀
    intro ε hε hεr
    simpa only [zero_mul,add_zero] using hbound ε hε hεr
  refine ⟨2*Λ,mul_ne_zero (by norm_num) hΛ,?_⟩
  have hh := (hf.const_mul (2:ℂ)).add hg
  simp only [add_zero] at hh
  convert hh using 1
  funext ε
  simp only [Complex.real_smul,g,f]
  ring

end
end IsingBulk.Preferred22
