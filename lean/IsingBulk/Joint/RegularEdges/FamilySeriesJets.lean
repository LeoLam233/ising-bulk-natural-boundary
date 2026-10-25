import IsingBulk.Joint.RegularEdges.FamilyTailJets
import IsingBulk.Joint.RegularEdges.FullSeriesJets

/-! # Common-family full parity derivative series, with the finite prefix intact -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.FormFactors Set Filter Metric
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_paritySeries_local_jets {b : ℝ} (B S : ℂ × E→ℂ) {Q : Set E}
    (hb : |b|<1) (hQ : IsCompact Q) (hBa : ∀eta∈Q, AnalyticAt ℂ B (0,eta))
    (hSa : ∀eta∈Q, AnalyticAt ℂ S (0,eta))
    (hB : ∀eta∈Q, 0<(B (0,eta)).im) (hS0 : ∀eta∈Q, S (0,eta)≠0) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q, ∀ e : ℕ, ∀ u : ℂ, ‖u‖<δ → 0<u.im →
      AnalyticAt ℂ (paritySeries e b (fun t=>B (t,eta)) (fun t=>S (t,eta))) u ∧
      ∀ j : ℕ, HasSum (fun i => iteratedDeriv j
        (angularCoefficient (2*i+e) b (fun t=>B (t,eta)) (fun t=>S (t,eta))) u)
        (iteratedDeriv j (paritySeries e b (fun t=>B (t,eta)) (fun t=>S (t,eta))) u) := by
  obtain ⟨ρ,hρ,htube⟩ := compact_admissible_family_tube B S hQ hBa hSa hB hS0
  obtain ⟨δ,hδ,hjets⟩ := compact_family_full_coefficient_tails B S hb hQ hBa hSa hB hS0
  obtain ⟨G,hG,_,hbound⟩ := hjets 0
  refine ⟨min ρ δ,lt_min hρ hδ,?_⟩
  intro eta heta e u hu hi
  let U : Set ℂ := {v | ‖v‖<min ρ δ ∧ 0<v.im}
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have huU : u∈U := ⟨hu,hi⟩
  have hud : ‖u‖<δ := hu.trans_le (min_le_right _ _)
  have hBa' : AnalyticOnNhd ℂ (fun t=>B (t,eta)) U := by
    intro v hv
    exact (htube eta heta v (hv.1.trans_le (min_le_left _ _)).le).1.comp
      (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hSa' : AnalyticOnNhd ℂ (fun t=>S (t,eta)) U := by
    intro v hv
    exact (htube eta heta v (hv.1.trans_le (min_le_left _ _)).le).2.1.comp
      (f := fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hup : ∀v∈U,0<v.im := fun _ hv=>hv.2
  have hBi : ∀v∈U,0<(B (v,eta)).im := fun v hv=>(htube eta heta v (hv.1.trans_le (min_le_left _ _)).le).2.2.1
  have hS : ∀v∈U,S (v,eta)≠0 := fun v hv=>(htube eta heta v (hv.1.trans_le (min_le_left _ _)).le).2.2.2
  let H : ℕ → ℝ := fun n => if n < 3 then ‖angularCoefficient n b (fun t=>B (t,eta)) (fun t=>S (t,eta)) u‖+1 else G (n-3)
  have hH : Summable H := by
    apply (summable_nat_add_iff 3).mp
    simpa [H] using hG
  have hlow : ∀ᶠ v in 𝓝 u, ∀ n ∈ Finset.range 3,
      ‖angularCoefficient n b (fun t=>B (t,eta)) (fun t=>S (t,eta)) v‖ ≤ ‖angularCoefficient n b (fun t=>B (t,eta)) (fun t=>S (t,eta)) u‖+1 := by
    rw [Finset.eventually_all]
    intro n _
    exact ((angularCoefficient_analyticAt hU hBa' hSa' hup hBi hS n huU).continuousAt.norm.eventually_lt
      continuousAt_const (by linarith)).mono (fun _ h => h.le)
  have hev : ∀ᶠ v in 𝓝 u, v ∈ U ∧ ‖v‖ < δ ∧
      ∀ n, ‖angularCoefficient n b (fun t=>B (t,eta)) (fun t=>S (t,eta)) v‖ ≤ H n := by
    filter_upwards [hU.mem_nhds huU,((continuous_norm).isOpen_preimage _ isOpen_Iio).mem_nhds hud,hlow]
      with v hv hvd hvlow
    refine ⟨hv,hvd,?_⟩
    intro n
    dsimp [H]
    split_ifs with hn
    · exact hvlow n (Finset.mem_range.mpr hn)
    · have ht := hbound eta heta v hvd hv.2 (n-3)
      have he : 2*0+3+(n-3)=n := by omega
      simpa only [he,iteratedDeriv_zero] using ht
  obtain ⟨V,hVsub,hVo,huV⟩ := _root_.mem_nhds_iff.mp hev
  have hsub : V ⊆ U := fun v hv => (hVsub hv).1
  have hcoef (n : ℕ) : AnalyticOnNhd ℂ (angularCoefficient n b (fun t=>B (t,eta)) (fun t=>S (t,eta))) V :=
    fun v hv => angularCoefficient_analyticAt hU hBa' hSa' hup hBi hS n (hsub hv)
  have hsel : Summable (fun i => H (2*i+e)) := hH.comp_injective (by intro a b h; dsimp at h; omega)
  have hnorm (i : ℕ) (v : ℂ) (hv : v∈V) : ‖angularCoefficient (2*i+e) b (fun t=>B (t,eta)) (fun t=>S (t,eta)) v‖ ≤ H (2*i+e) :=
    (hVsub hv).2.2 _
  constructor
  · exact (Complex.differentiableOn_tsum_of_summable_norm hsel
      (fun i v hv => (hcoef (2*i+e) v hv).differentiableAt.differentiableWithinAt)
      hVo hnorm).analyticOnNhd hVo u huV
  · intro j
    exact hasSum_iteratedDeriv_of_summable_envelope hVo (fun i => hcoef (2*i+e)) hsel hnorm j huV

end
end IsingBulk.Joint.RegularEdges
