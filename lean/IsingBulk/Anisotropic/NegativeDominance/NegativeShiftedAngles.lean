import IsingBulk.Anisotropic.NegativeDominance.NegativeNumeratorBridge
import IsingBulk.Anisotropic.RegularEdges.IntegratedJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter MeasureTheory
open scoped BigOperators Topology

def negativeShiftedAngles (n : ℕ) (v : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun i => wrapAngle (physicalDependentAngles n (fun k => v k+Real.pi) i-Real.pi)

@[simp] theorem negativeShiftedAngles_castSucc (n : ℕ) (v : Fin n → ℝ) (i : Fin n) :
    negativeShiftedAngles n v i.castSucc=wrapAngle (v i) := by
  simp [negativeShiftedAngles,physicalDependentAngles]

theorem negativeShiftedAngles_last (n : ℕ) (v : Fin n → ℝ) :
    negativeShiftedAngles n v (Fin.last n)=wrapAngle (-(∑ i, v i)-(n+1 : ℕ)*Real.pi) := by
  simp only [negativeShiftedAngles,physicalDependentAngles,Fin.snoc_last,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  push_cast
  ring

theorem negativeShiftedAngles_retained_norm (m k : ℕ) (v : Fin (m+k) → ℝ)
    (hv : ∀ i, v i∈Icc (-Real.pi) Real.pi) :
    ‖fun i : Fin m => negativeShiftedAngles (m+k) v ((Fin.castAdd k i).castSucc)‖=
      ‖fun i : Fin m => v (Fin.castAdd k i)‖ := by
  simp only [negativeShiftedAngles_castSucc]
  rw [Pi.norm_def,Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  exact NNReal.eq (norm_wrapAngle_of_mem (hv (Fin.castAdd k i)))

theorem edgeFullIntegrand_wrapAngle {N : ℕ} (b : ℝ) (B S : ℂ → ℂ)
    (u : ℂ) (q : Fin N → ℝ) :
    edgeFullIntegrand b B S u (fun i => wrapAngle (q i))=edgeFullIntegrand b B S u q := by
  unfold edgeFullIntegrand edgeRootProduct
  rw [show List.ofFn (fun i => wrapAngle (q i))=(List.ofFn q).map wrapAngle by rw [List.map_ofFn]; rfl]
  rw [edgeNumerator_map_wrapAngle]
  simp only [edgeParamRoot_wrapAngle]

/-- Direct translation of the complete original box. Unlike period shifting,
this requires no periodicity, integrability or continuity premise. -/
theorem angleBox_integral_eq_negative_shifted (n : ℕ) (f : (Fin n → ℝ) → ℂ) :
    (∫ q in angleBox n, f q)=
      ∫ v in Icc (fun _ => -Real.pi) (fun _ => Real.pi), f (fun i => v i+Real.pi) := by
  let c : Fin n → ℝ := fun _ => Real.pi
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  have hm (v : Fin n → ℝ) : v+c∈angleBox n ↔ v∈K := by
    constructor <;> intro h <;> constructor <;> intro i
    · have hh := h.1 i
      change 0≤v i+Real.pi at hh
      linarith
    · have hh := h.2 i
      change v i+Real.pi≤2*Real.pi at hh
      linarith
    · have hh := h.1 i
      change 0≤v i+Real.pi
      linarith
    · have hh := h.2 i
      change v i+Real.pi≤2*Real.pi
      linarith
  have he : (fun v => (angleBox n).indicator f (v+c))=K.indicator (fun v => f (v+c)) := by
    funext v
    by_cases hv : v∈K
    · simp only [indicator_of_mem hv,indicator_of_mem ((hm v).mpr hv)]
    · simp only [indicator_of_notMem hv,indicator_of_notMem (not_congr (hm v) |>.mpr hv)]
  have ht := integral_add_right_eq_self (μ := volume) ((angleBox n).indicator f) c
  rw [he,integral_indicator measurableSet_Icc] at ht
  rw [integral_indicator (show MeasurableSet (angleBox n) from measurableSet_Icc)] at ht
  exact ht.symm

def negativeShiftedFullIntegrand (b : ℝ) (B S : ℂ → ℂ) (n : ℕ)
    (u : ℂ) (v : Fin n → ℝ) : ℂ := edgeFullIntegrand b B S u (negativeShiftedAngles n v)

/-- Genuine shifted-family jet estimates retain the same dimension-free
constants as the full angular integrand estimates. -/
theorem negativeShiftedFullIntegrand_uniform_jets {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ ε : ℝ, 0<ε → ε<δ → ∀ (m k : ℕ) [Nonempty (Fin m)]
        (v : Fin (m+k) → ℝ), (∀ i, v i∈Icc (-Real.pi) Real.pi) →
        (fun i : Fin m => v (Fin.castAdd k i))≠0 →
        ‖iteratedDeriv j (fun u => negativeShiftedFullIntegrand b B S (m+k) u v)
          (Complex.I*(ε : ℂ))‖≤D*particleEdgeMajorant r C M (m+k+1)*(m+k+1 : ℕ)^j*
            (1+‖fun i : Fin m => v (Fin.castAdd k i)‖^(-(2*(j+1) : ℝ))) := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,h⟩ := edgeFullIntegrand_uniform_jets hb hB hc hS hS0 j
  refine ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,?_⟩
  intro ε hε he m k _ v hv hv0
  have hn := negativeShiftedAngles_retained_norm m k v hv
  have hp : (fun i : Fin m => negativeShiftedAngles (m+k) v ((Fin.castAdd k i).castSucc))≠0 := by
    intro hz
    have hn0 : ‖fun i : Fin m => v (Fin.castAdd k i)‖=0 := by rw [← hn,hz,norm_zero]
    exact hv0 (norm_eq_zero.mp hn0)
  have hh := h ε hε he (m+k+1) m (negativeShiftedAngles (m+k) v)
    (fun i => (Fin.castAdd k i).castSucc) (fun _ => wrapAngle_mem _) hp
  rw [hn] at hh
  exact hh

end
end IsingBulk.Anisotropic.NegativeDominance
