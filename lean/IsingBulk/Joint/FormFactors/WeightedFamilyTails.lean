import IsingBulk.Joint.FormFactors.ParametricCoefficientTails
import IsingBulk.Joint.RegularEdges.WeightedFullSum

/-! Genuine mixed parameter tails with all integer physical particle weights.
The local square root is constructed, and cancels from the final statement. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Joint.RegularEdges

def familyOddTerm (b : ℝ) (B S P amp : Coupling → ℂ) (n : ℕ) (q : Coupling) : ℂ :=
  amp q*(P q)^n*independentAngularCoefficient (2*n) b (q.1,(B q,S q))
def familyEvenTerm (b : ℝ) (B S P amp : Coupling → ℂ) (n : ℕ) (q : Coupling) : ℂ :=
  amp q*(P q)^(n+1)*independentAngularCoefficient (2*n+1) b (q.1,(B q,S q))

theorem independentCoefficient_rescale (n : ℕ) (b : ℝ) (u B S R : ℂ) :
    independentAngularCoefficient n b (u,(B,S/R))=
      R^(n+1)*independentAngularCoefficient n b (u,(B,S)) :=
  angularCoefficient_rescale n b (fun _ => B) (fun _ => S) (fun _ => R) u

theorem familyOddTerm_rescale {B S P amp R : Coupling → ℂ} (b : ℝ) (n : ℕ)
    (q : Coupling) (hs : R q^2=P q) (hn : R q≠0) :
    amp q/R q*independentAngularCoefficient (2*n) b (q.1,(B q,S q/R q))=
      familyOddTerm b B S P amp n q := by
  rw [independentCoefficient_rescale,pow_add,pow_mul,hs,pow_one]
  unfold familyOddTerm
  field_simp

theorem familyEvenTerm_rescale {B S P amp R : Coupling → ℂ} (b : ℝ) (n : ℕ)
    (q : Coupling) (hs : R q^2=P q) :
    amp q*independentAngularCoefficient (2*n+1) b (q.1,(B q,S q/R q))=
      familyEvenTerm b B S P amp n q := by
  rw [independentCoefficient_rescale,show 2*n+1+1=2*(n+1) by omega,pow_mul,hs]
  simp only [familyEvenTerm,mul_assoc]

/-- Both complete normalized parity tails have a common complex parameter
neighborhood, chosen before the mixed derivative order. -/
theorem local_weighted_coefficient_tails {b : ℝ} (hb : |b|<1)
    {q₀ : Coupling} (hq₀ : q₀.1=0) {B S P amp : Coupling → ℂ}
    (hBa : AnalyticAt ℂ B q₀) (hSa : AnalyticAt ℂ S q₀)
    (hPa : AnalyticAt ℂ P q₀) (haa : AnalyticAt ℂ amp q₀)
    (hB : 0<(B q₀).im) (hS : S q₀≠0) (hP : P q₀≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G H : ℕ→ℝ,
      Summable G ∧ Summable H ∧ (∀ k, 0≤G k) ∧ (∀ k, 0≤H k) ∧
      ∀ q∈ball q₀ δ, 0<q.1.im → ∀ k : ℕ,
      ‖iteratedFDeriv ℂ j (familyOddTerm b B S P amp (j+2+k)) q‖≤G k ∧
      ‖iteratedFDeriv ℂ j (familyEvenTerm b B S P amp (j+1+k)) q‖≤H k := by
  let R : Coupling → ℂ := fun q => Complex.sqrt (P q₀)*Complex.sqrt (P q/P q₀)
  have hRs (q : Coupling) : R q^2=P q := by
    simp only [R,mul_pow,Complex.sqrt,Complex.cpow_ofNat_inv_pow]
    field_simp
  have hRn : R q₀≠0 := by intro hz; have hh := hRs q₀; rw [hz,zero_pow (by norm_num)] at hh; exact hP hh.symm
  have hRa : AnalyticAt ℂ R q₀ := by
    apply analyticAt_const.mul
    have hs : AnalyticAt ℂ Complex.sqrt (P q₀/P q₀) := by
      rw [div_self hP]
      exact Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane 1 Complex.one_mem_slitPlane
    exact AnalyticAt.fun_comp_of_eq (f := fun q : Coupling => P q/P q₀) (g := Complex.sqrt) hs hPa.div_const rfl
  have he : ∀ᶠ q in 𝓝 q₀, AnalyticAt ℂ B q ∧ AnalyticAt ℂ S q ∧ AnalyticAt ℂ R q ∧
      AnalyticAt ℂ amp q ∧ 0<(B q).im ∧ S q≠0 ∧ R q≠0 :=
    hBa.eventually_analyticAt.and (hSa.eventually_analyticAt.and
      (hRa.eventually_analyticAt.and (haa.eventually_analyticAt.and
        ((continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hBa.continuousAt) hB).and
          ((hSa.continuousAt.eventually_ne hS).and (hRa.continuousAt.eventually_ne hRn))))))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp he
  let C : Set Coupling := closedBall q₀ (r/2)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCq : C∈𝓝 q₀ := closedBall_mem_nhds _ (half_pos hr)
  have hd (q : Coupling) (hq : q∈C) := hrsub
    (show q∈ball q₀ r from (show dist q q₀≤r/2 from hq).trans_lt (by linarith))
  let f : Coupling → NumeratorParameter := fun q => (q.1,(B q,S q/R q))
  have hf : AnalyticOnNhd ℂ f C := by
    intro q hq
    exact analyticAt_fst.prod ((hd q hq).1.prod
      ((hd q hq).2.1.div (hd q hq).2.2.1 (hd q hq).2.2.2.2.2.2))
  have ha : AnalyticOnNhd ℂ amp C := fun q hq => (hd q hq).2.2.2.1
  have har : AnalyticOnNhd ℂ (fun q => amp q/R q) C := by
    intro q hq
    exact (ha q hq).div (hd q hq).2.2.1 (hd q hq).2.2.2.2.2.2
  have hfb : ∀ q∈C, 0<(f q).2.1.im := fun q hq => (hd q hq).2.2.2.2.1
  have hfs : ∀ q∈C, (f q).2.2≠0 := fun q hq =>
    div_ne_zero (hd q hq).2.2.2.2.2.1 (hd q hq).2.2.2.2.2.2
  obtain ⟨δ₁,hδ₁,hodd⟩ := compact_parametric_coefficient_tails hb hC hCq hq₀ hf har (by intros; rfl) hfb hfs
  obtain ⟨δ₂,hδ₂,heven⟩ := compact_parametric_coefficient_tails hb hC hCq hq₀ hf ha (by intros; rfl) hfb hfs
  let δ := min (min δ₁ δ₂) (r/2)
  have hδ : 0<δ := lt_min (lt_min hδ₁ hδ₂) (half_pos hr)
  refine ⟨δ,hδ,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hGb⟩ := hodd j
  obtain ⟨H,hH,hH0,hHb⟩ := heven j
  refine ⟨fun k => G (2*k+1),fun k => H (2*k),
    hG.comp_injective (by intro a c he; dsimp at he; omega),
    hH.comp_injective (by intro a c he; dsimp at he; omega),
    fun k => hG0 _,fun k => hH0 _,?_⟩
  intro q hq hi k
  have hq₁ : q∈ball q₀ δ₁ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hq
  have hq₂ : q∈ball q₀ δ₂ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hq
  have hqC : q∈C := (ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))) hq
  have hRneq : ∀ᶠ t in 𝓝 q, R t≠0 :=
    (hd q hqC).2.2.1.continuousAt.eventually_ne (hd q hqC).2.2.2.2.2.2
  constructor
  · have heq : (fun t => amp t/R t*independentAngularCoefficient (2*(j+2+k)) b (f t)) =ᶠ[𝓝 q]
        familyOddTerm b B S P amp (j+2+k) := hRneq.mono (fun t ht => familyOddTerm_rescale b _ t (hRs t) ht)
    rw [←(heq.iteratedFDeriv ℂ j).eq_of_nhds]
    have hh := hGb q hq₁ hi (2*k+1)
    rw [show 2*j+3+(2*k+1)=2*(j+2+k) by omega] at hh
    exact hh
  · have heq : (fun t => amp t*independentAngularCoefficient (2*(j+1+k)+1) b (f t)) =
        familyEvenTerm b B S P amp (j+1+k) := funext (fun t => familyEvenTerm_rescale b _ t (hRs t))
    rw [←heq]
    have hh := hHb q hq₂ hi (2*k)
    rw [show 2*j+3+2*k=2*(j+1+k)+1 by omega] at hh
    exact hh

end
end IsingBulk.Joint.FormFactors
