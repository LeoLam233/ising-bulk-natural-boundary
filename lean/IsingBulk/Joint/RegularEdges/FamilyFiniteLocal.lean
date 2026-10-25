import IsingBulk.Joint.RegularEdges.FamilyFiniteGap

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem edgeSincFactor_norm_le_one {N : ℕ} (q : Fin N→ℝ) : ‖edgeSincFactor q‖≤1 := by
  unfold edgeSincFactor
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro p _
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)

/-- One common complex polydisk for the actual analytic factors and derivative
numerator, before any compact-family member is chosen. -/
theorem compact_family_local_factors {N : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) (j : ℕ) :
    ∃r M : ℝ,0<r ∧ 0<M ∧ ∀eta∈Q,∀u : ℂ,∀q : Fin N→ℂ,‖u‖<r → ‖q‖<r →
      AnalyticAt ℂ (familyEdgeAmplitude b B S) (u,(eta,q)) ∧
      AnalyticAt ℂ (familyEdgeDenominator b B) (u,(eta,q)) ∧
      ‖familyEdgeJet b B S j (u,(eta,q))‖≤M := by
  let G : (ℂ × (Fin N→ℂ)) × E → ℂ × (E × (Fin N→ℂ)) :=
    fun p => (p.1.1,(p.2,p.1.2))
  have hG : Continuous G := by unfold G; fun_prop
  let U := {p : (ℂ × (Fin N→ℂ)) × E |
    AnalyticAt ℂ (familyEdgeAmplitude b B S) (G p) ∧
    AnalyticAt ℂ (familyEdgeDenominator b B) (G p)}
  have hU : IsOpen U := ((isOpen_analyticAt ℂ (familyEdgeAmplitude b B S)).inter
    (isOpen_analyticAt ℂ (familyEdgeDenominator b B))).preimage hG
  obtain ⟨a,ha,hatube⟩ := Negative.compact_product_tube hQ hU (by
    intro eta heta
    constructor
    · simpa only [G,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Complex.ofReal_zero,Pi.zero_def] using (familyEdgeAmplitude_analyticAt_real (N:=N) hb (hB eta heta)
        (hBi eta heta) (hS eta heta) (hS0 eta heta) 0)
    · simpa only [G,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Complex.ofReal_zero,Pi.zero_def] using (familyEdgeDenominator_analyticAt_real (N:=N) hb (hB eta heta) (hBi eta heta) 0))
  obtain ⟨r,M,hr,hM,hJ⟩ := Negative.compact_analytic_uniform_bound
    (fun p : (ℂ × (Fin N→ℂ)) × E => familyEdgeJet b B S j (G p)) hQ (by
      intro eta heta
      have hj : AnalyticAt ℂ (familyEdgeJet b B S j) (G (0,eta)) := by
        simpa only [G,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Complex.ofReal_zero,Pi.zero_def] using (familyEdgeJet_analyticAt_real (N:=N) hb (hB eta heta)
          (hBi eta heta) (hS eta heta) (hS0 eta heta) 0 j)
      exact hj.comp (f:=G) (x:=(0,eta))
        ((analyticAt_fst.comp analyticAt_fst).prod (analyticAt_snd.prod (analyticAt_snd.comp analyticAt_fst))))
  refine ⟨min a r,M,lt_min ha hr,hM,?_⟩
  intro eta heta u q hu hq
  have har : ‖(u,q)‖<a := by rw [Prod.norm_def]; exact max_lt (hu.trans_le (min_le_left _ _)) (hq.trans_le (min_le_left _ _))
  have hrr : ‖(u,q)‖<r := by rw [Prod.norm_def]; exact max_lt (hu.trans_le (min_le_right _ _)) (hq.trans_le (min_le_right _ _))
  exact ⟨(hatube eta heta (u,q) har).1,(hatube eta heta (u,q) har).2,(hJ eta heta (u,q) hrr).2.le⟩

/-- The actual shape derivative identity holds on one common neighborhood,
for every compact-family member and every derivative order. -/
theorem compact_family_shape_derivative_neighborhood {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0) :
    ∃r : ℝ,0<r ∧ ∀eta∈Q,∀t : ℝ,|t|<r → ∀x : ShapeSpace n,‖x‖<r →
      edgeShapeDenominator b (fun u=>B (u,eta)) t x≠0 → ∀j : ℕ,
      iteratedDeriv j (fun u=>edgeAngularDensity b (fun u=>B (u,eta)) (fun u=>S (u,eta))
        u (fun i=>x.1 i)) (Complex.I*(t:ℂ)^2)=
        (shapeVandermondeSq x:ℂ)*edgeShapeAmplitude b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j t x/
          edgeShapeDenominator b (fun u=>B (u,eta)) t x^(j+1) := by
  obtain ⟨r,M,hr,_hM,hfac⟩ := compact_family_local_factors (N:=n+1) B S hb hQ hB hBi hS hS0 0
  refine ⟨min 1 r,lt_min zero_lt_one hr,?_⟩
  intro eta heta t ht x hx hne j
  have ht1 : |t|<1 := ht.trans_le (min_le_left _ _)
  have htr : |t|<r := ht.trans_le (min_le_right _ _)
  have hu : ‖Complex.I*(t:ℂ)^2‖<r := by
    simp only [norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [abs_nonneg t]
  have hq : ‖fun i => (x.1 i:ℂ)‖<r := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_ |>.trans_lt (hx.trans_le (min_le_right _ _))
    intro i
    rw [Complex.norm_real]
    exact PiLp.norm_apply_le x.1 i
  obtain ⟨ha,hd,_⟩ := hfac eta heta _ _ hu hq
  have hmap : AnalyticAt ℂ (fun u : ℂ => (u,(eta,fun i => (x.1 i:ℂ)))) (Complex.I*(t:ℂ)^2) :=
    analyticAt_id.prod analyticAt_const
  have hh := edgeAngularDensity_iteratedDeriv b (fun u=>B (u,eta)) (fun u=>S (u,eta))
    (fun i=>x.1 i) (Complex.I*(t:ℂ)^2) j
    (ha.comp (f:=fun u : ℂ => (u,(eta,fun i => (x.1 i:ℂ)))) hmap)
    (hd.comp (f:=fun u : ℂ => (u,(eta,fun i => (x.1 i:ℂ)))) hmap) hne
  simpa only [shapeVandermondeSq,Complex.ofReal_pow,edgeShapeAmplitude,edgeShapeDenominator,mul_assoc] using hh

end
end IsingBulk.Joint.RegularEdges
