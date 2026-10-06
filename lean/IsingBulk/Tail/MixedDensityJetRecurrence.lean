import IsingBulk.Analysis.JetsBoundCalculus
import IsingBulk.Analysis.JetsFiniteSum

/-! Finite jets of the sparse mixed regular density operator. Only two
spatial residual directions occur; iteration costs polynomial powers of N. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mixedRegularDensityStep (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ) (x : E) : ℂ :=
  fderiv ℂ F x e₀+R₁ x*fderiv ℂ F x e₁+R₂ x*fderiv ℂ F x e₂+
    (fderiv ℂ R₁ x e₁+fderiv ℂ R₂ x e₂)*F x

theorem mixedRegularDensityStep_jet_bound (e₀ e₁ e₂ : E) (he₀ : ‖e₀‖≤1)
    (he₁ : ‖e₁‖≤1) (he₂ : ‖e₂‖≤1) (R₁ R₂ F : E → ℂ) (x : E)
    (J : ℕ) (C D : ℝ) (hR₁ : JetBound R₁ x (J+1) C)
    (hR₂ : JetBound R₂ x (J+1) C) (hF : JetBound F x (J+1) D) :
    JetBound (mixedRegularDensityStep e₀ e₁ e₂ R₁ R₂ F) x J ((1+4*2^J*C)*D) := by
  have h₀ := hF.direction e₀ he₀
  have h₁ := (hR₁.mono (Nat.le_succ J) le_rfl).mul (hF.direction e₁ he₁)
  have h₂ := (hR₂.mono (Nat.le_succ J) le_rfl).mul (hF.direction e₂ he₂)
  have hd := ((hR₁.direction e₁ he₁).add (hR₂.direction e₂ he₂)).mul
    (hF.mono (Nat.le_succ J) le_rfl)
  have hh := ((h₀.add h₁).add h₂).add hd
  exact hh.mono le_rfl (by ring_nf; exact le_rfl)

theorem mixedRegularDensityStep_iterated_jets (e₀ e₁ e₂ : E) (he₀ : ‖e₀‖≤1)
    (he₁ : ‖e₁‖≤1) (he₂ : ‖e₂‖≤1) (R₁ R₂ F : E → ℂ) (x : E)
    (J : ℕ) (C D : ℝ) (hR₁ : JetBound R₁ x (J+1) C)
    (hR₂ : JetBound R₂ x (J+1) C) (hF : JetBound F x J D) :
    ∀ k≤J,JetBound ((mixedRegularDensityStep e₀ e₁ e₂ R₁ R₂)^[k] F)
      x (J-k) ((1+4*2^J*C)^k*D) := by
  intro k
  induction k with
  | zero => intro _; simpa using hF
  | succ k ih =>
    intro hk
    have hkJ : k≤J := by omega
    have hp := ih hkJ
    have hR₁' := hR₁.mono (show J-(k+1)+1≤J+1 by omega) le_rfl
    have hR₂' := hR₂.mono (show J-(k+1)+1≤J+1 by omega) le_rfl
    have hF' := hp.mono (show J-(k+1)+1≤J-k by omega) le_rfl
    have hh := mixedRegularDensityStep_jet_bound e₀ e₁ e₂ he₀ he₁ he₂ R₁ R₂ _ x
      (J-(k+1)) C _ hR₁' hR₂' hF'
    rw [Function.iterate_succ_apply']
    apply hh.mono le_rfl
    have hc := hR₁.nonneg
    have hD := hF.nonneg
    have hpow : (2:ℝ)^(J-(k+1))≤2^J := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    have hcost : 1+4*(2:ℝ)^(J-(k+1))*C≤1+4*2^J*C := by gcongr
    calc
      _ ≤ (1+4*2^J*C)*((1+4*2^J*C)^k*D) :=
        mul_le_mul_of_nonneg_right hcost (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- If each residual jet costs N C, the fixed iteration window introduces
only N^k, never an exponential-in-N² coefficient loss. -/
theorem mixed_density_iteration_dimension_cost (J k N : ℕ) (hN : 1≤N)
    {C D : ℝ} (hC : 1≤C) (hD : 0≤D) :
    (1+4*2^J*((N:ℝ)*C))^k*D≤((1+4*2^J)*C)^k*(N:ℝ)^k*D := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hnc : 1≤(N:ℝ)*C := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hC)]
  have hbase : 1+4*(2:ℝ)^J*((N:ℝ)*C)≤((1+4*2^J)*C)*(N:ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+4*(2:ℝ)^J*((N:ℝ)*C)) hbase k
  rw [mul_pow] at hp
  exact mul_le_mul_of_nonneg_right hp hD

structure MixedDensityJetTerm (N : ℕ) (E : Type*) where
  cutoff : List (Fin N)
  regularPart : E → ℂ

def MixedDensityJetTerm.child {N : ℕ} (T : MixedDensityJetTerm N E)
    (e₀ e₁ e₂ : E) (R₁ R₂ : E → ℂ) (V : Fin N → E → ℂ) : Option (Fin N) → MixedDensityJetTerm N E
  | none => ⟨T.cutoff,mixedRegularDensityStep e₀ e₁ e₂ R₁ R₂ T.regularPart⟩
  | some i => ⟨i::T.cutoff,fun x => -V i x*T.regularPart x⟩

def mixedDensityActions (N : ℕ) : List (Option (Fin N)) := none::(List.finRange N).map some

def mixedDensityJetTerms {N : ℕ} (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ)
    (V : Fin N → E → ℂ) : ℕ → List (MixedDensityJetTerm N E)
  | 0 => [⟨[],F⟩]
  | k+1 => (mixedDensityJetTerms e₀ e₁ e₂ R₁ R₂ F V k).flatMap
      (fun T => (mixedDensityActions N).map (T.child e₀ e₁ e₂ R₁ R₂ V))

theorem mixedDensityJetTerms_length {N : ℕ} (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ)
    (V : Fin N → E → ℂ) (k : ℕ) :
    (mixedDensityJetTerms e₀ e₁ e₂ R₁ R₂ F V k).length=(N+1)^k := by
  induction k with
  | zero => simp [mixedDensityJetTerms]
  | succ k ih => simp [mixedDensityJetTerms,List.length_flatMap,mixedDensityActions,ih,pow_succ]

theorem mixedDensityJetTerms_cutoff_length {N : ℕ} (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ)
    (V : Fin N → E → ℂ) (k : ℕ) :
    ∀ T∈mixedDensityJetTerms e₀ e₁ e₂ R₁ R₂ F V k,T.cutoff.length≤k := by
  induction k with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [mixedDensityJetTerms,List.mem_singleton] using hT
    subst T
    simp
  | succ k ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hh := ih P hP
    cases a <;> simp only [MixedDensityJetTerm.child,List.length_cons] <;> omega

theorem mixedDensityJetTerms_jet_budget {N : ℕ} (e₀ e₁ e₂ : E)
    (he₀ : ‖e₀‖≤1) (he₁ : ‖e₁‖≤1) (he₂ : ‖e₂‖≤1)
    (R₁ R₂ F : E → ℂ) (V : Fin N → E → ℂ) (x : E)
    (J k : ℕ) (hk : k≤J) (C D : ℝ) (hC : 1≤C)
    (hR₁ : JetBound R₁ x (J+1) C) (hR₂ : JetBound R₂ x (J+1) C)
    (hV : ∀ i,JetBound (V i) x J C) (hF : JetBound F x J D) :
    ∀ T∈mixedDensityJetTerms e₀ e₁ e₂ R₁ R₂ F V k,
      JetBound T.regularPart x (J-k) ((1+4*2^J*C)^k*D) := by
  induction k with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [mixedDensityJetTerms,List.mem_singleton] using hT
    subst T
    simpa using hF
  | succ k ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hp := ih (by omega) P hP
    have hc : 0≤C := by linarith
    have hD := hp.nonneg
    have hpow : (2:ℝ)^(J-(k+1))≤2^J := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    cases a with
    | none =>
      have hh := mixedRegularDensityStep_jet_bound e₀ e₁ e₂ he₀ he₁ he₂ R₁ R₂ P.regularPart x
        (J-(k+1)) C _ (hR₁.mono (by omega) le_rfl) (hR₂.mono (by omega) le_rfl)
        (hp.mono (by omega) le_rfl)
      apply hh.mono le_rfl
      have hcost : 1+4*(2:ℝ)^(J-(k+1))*C≤1+4*2^J*C := by gcongr
      calc
        _ ≤ (1+4*2^J*C)*((1+4*2^J*C)^k*D) := mul_le_mul_of_nonneg_right hcost hD
        _ = _ := by rw [pow_succ]; ring
    | some i =>
      have hh := ((hV i).mono (show J-(k+1)≤J by omega) le_rfl).neg.mul
        (hp.mono (show J-(k+1)≤J-k by omega) le_rfl)
      apply hh.mono le_rfl
      have hcost : (2:ℝ)^(J-(k+1))*C≤1+4*2^J*C := by
        have hh := mul_le_mul_of_nonneg_right hpow hc
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) J) hc]
      calc
        _ ≤ (1+4*2^J*C)*((1+4*2^J*C)^k*D) := mul_le_mul_of_nonneg_right hcost hD
        _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.Tail
