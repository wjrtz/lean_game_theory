import Common
import Mathlib.Data.Real.NNReal

/-
Formalization of Nash's Theorem.
Based on Kesselheim, T.: Lecture notes for algorithmic game theory (2017)
-/

noncomputable section
set_option autoImplicit false
open Finset
open Pointwise
open NNReal
open BigOperators DirectSum

open Classical
open Function

universe u

/- We assume Brouwer's fixed point theorem -/
theorem brouwer_fixed_point {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : s → s), Continuous f → ∃ x, f.IsFixedPt x := by sorry

/- A lemma missing from mathlib -/
lemma compact_sum {α β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β] {s : Finset α} {f : α → Set β} (h : ∀ a, IsCompact (f a))
  : IsCompact (∑ a in s, f a) := by {
  induction s using Finset.induction with
  | empty => exact Set.finite_zero.isCompact
  | insert notmem ih =>
    rw [sum_insert notmem]
    apply IsCompact.add (h _) ih
}

/-
We rule our own PMF definition. Differences to PMF from mathlib:
- co-domain ℝ
- Finset.sum instead of HasSum
-/
def PMF (α : Type u) [Fintype α] := {p : α → ℝ // (∀ a, p a ≥ 0) ∧ ∑ a, p a = 1}

namespace PMF

variable {α : Type u} [Fintype α]

instance : TopologicalSpace (PMF α) := instTopologicalSpaceSubtype

instance : FunLike (PMF α) α fun _ => ℝ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[ext]
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  FunLike.ext p q h

theorem nonneg (p : PMF α): ∀ a, p a ≥ 0
  := p.2.left

theorem sum_coe_eq_one (p : PMF α) : ∑ a, p a = 1
  := p.2.right

lemma coe_ne_zero (p : PMF α) : FunLike.coe p ≠ 0 := by {
  intro p0
  have := sum_coe_eq_one p
  rw [p0] at this
  simp only [Pi.zero_apply, sum_const_zero, zero_ne_one] at this
}

def pure (a : α) : PMF α :=
  ⟨fun a' => if a' = a then 1 else 0,
   ⟨by intro a'; by_cases a' = a <;> simp [h],
    by simp only [sum_ite_eq', mem_univ, ite_true]⟩⟩

theorem pure_apply (a a' : α) : pure a a' = if a' = a then 1 else 0 := rfl

def support (p : PMF α) : Finset α := univ.filter (fun a ↦ p a ≠ 0)

lemma support_nonempty (p : PMF α) : Finset.Nonempty p.support := by {
  obtain ⟨a, ane0⟩ := Function.ne_iff.mp p.coe_ne_zero
  use a
  simpa [support]
}

end PMF

/- Game in normal form
`player` type of players
`Π p, G.strategy p` is the strategy space -/
structure Game where
  player : Type u
  /- There is only  a finite number of players -/
  player_finite : Fintype player
  /- Maps player to his strategies -/
  strategy : player → Type u
  /- Each player has only a finite number of strategies -/
  strategy_finite : ∀ p, Fintype (strategy p)
  /- Each player has at least one strategy -/
  strategy_inhabited : ∀ p, Inhabited (strategy p)
  /- Takes player and combinantion of strategies, returns payoff -/
  payoff : player → (Π p, strategy p) → ℝ

namespace Game

variable {G : Game}

instance : Fintype G.player := G.player_finite

-- Player pure strategies
def player.pStrat (p : G.player) := G.strategy p

instance {p : G.player} : Fintype p.pStrat := G.strategy_finite p
instance {p : G.player} : Inhabited p.pStrat := G.strategy_inhabited p

-- Player mixed strategies
def player.mStrat (p : G.player) := PMF p.pStrat
instance {p : G.player} : Inhabited p.mStrat := ⟨PMF.pure default⟩
instance {p : G.player} : TopologicalSpace p.mStrat := PMF.instTopologicalSpacePMF

-- Game pure strategies
def pStrat (G : Game) := (Π p : G.player, p.pStrat)

instance : Fintype G.pStrat := by unfold pStrat; exact Pi.fintype
instance : Inhabited G.pStrat := ⟨fun _ ↦ default⟩

-- Game mixed strategies
def mStrat (G : Game) := Π p : G.player, p.mStrat

instance : Inhabited G.mStrat := ⟨fun _ ↦ default⟩
instance : TopologicalSpace G.mStrat := Pi.topologicalSpace

-- Game mixed strategies as a ℝ vector space
def mStratSpace (G : Game)
  := {Φ : (p : G.player) × p.pStrat → ℝ | (∀ v, Φ v ≥ 0) ∧ ∀ p, ∑ s, Φ ⟨p, s⟩ = 1}

namespace player.mStrat

instance {p : G.player} : FunLike p.mStrat p.pStrat fun _ ↦ ℝ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[ext] lemma ext {p : G.player} (σ τ : p.mStrat) (h : ∀ s : p.pStrat, σ s = τ s) : σ = τ := FunLike.ext σ τ h

end player.mStrat

-- Pure strategies payoff
def pPay (G : Game) : G.player → G.pStrat → ℝ := G.payoff
def player.pPay (p : G.player) := G.pPay p

-- Mixed strategies payoff
def mPay (p : G.player) (M : G.mStrat)
  := ∑ S : G.pStrat, (∏ q : G.player, (M q (S q))) * p.pPay S
def player.mPay (p : G.player) := G.mPay p

namespace player.pStrat

@[coe] def toMStrat {p : G.player} (s : p.pStrat) : p.mStrat
  := PMF.pure s

instance {p : G.player} : Coe p.pStrat p.mStrat := ⟨toMStrat⟩

@[simp] lemma toMStrat_apply {p : G.player} (s : p.pStrat) (t : p.pStrat)
  : (s : p.mStrat) t = if t = s then 1 else 0 := PMF.pure_apply s t

end pStrat

namespace mStrat

lemma sum_coe_eq_one {p : G.player} (σ : p.mStrat)
  : ∑ s, σ s = 1 := PMF.sum_coe_eq_one σ

lemma nonneg {p : G.player} (σ : p.mStrat) : ∀ s, σ s ≥ 0
  := PMF.nonneg σ

end mStrat

lemma mPay_apply {p : G.player} (M : G.mStrat)
  : p.mPay M = ∑ S : G.pStrat, (∏ q : G.player, (M q (S q))) * p.pPay S := rfl

lemma mPay_update {p : G.player} (M : G.mStrat) (σ : p.mStrat)
  : p.mPay (update M p σ) = ∑ S : G.pStrat, (∏ q in univ.erase p, (M q (S q))) * σ (S p) * p.pPay S := by {
  rw [mPay_apply]
  congr; ext S
  congr
  rw [← prod_erase_mul _ _ (mem_univ p)]
  simp; left
  apply prod_congr rfl
  intro q qnep
  simp at qnep
  simp [qnep]
}

lemma mPay_update_eq {p : G.player} (M : G.mStrat) (σ : p.mStrat)
  : p.mPay (update M p σ) = ∑ s : p.pStrat, σ s * p.mPay (update M p s) := by {
  simp_rw [mPay_update, mul_sum, ← mul_assoc, mul_comm (σ _)]
  simp
  rw [← sum_finset_product' univ _ _ (by simp only [mem_univ, and_self, Prod.forall, forall_const])]
  let i (t : p.pStrat × G.pStrat) (_ : t ∈ univ.filter (fun t ↦ t.2 p = t.1)) : G.pStrat := t.2
  rw [← sum_filter, sum_bij i (fun ⟨_, S⟩ _ ↦ mem_univ S)]
  · intro ⟨s, S⟩ sS
    simp at sS ⊢
    subst sS
    tauto
  · intro ⟨s₁, S₁⟩ ⟨s₂, S₂⟩ s₁S₁ s₂S₂ S₁S₂
    simp at s₁S₁ s₂S₂ S₁S₂ ⊢
    rw [← s₁S₁, ← s₂S₂, S₁S₂]
    exact ⟨rfl, rfl⟩
  simp
}

lemma mPay_eq {p : G.player} (M : G.mStrat)
  : p.mPay M = ∑ s : p.pStrat, (M p) s * p.mPay (update M p s) := by {
  nth_rw 1 [← update_eq_self p M, mPay_update_eq]
}

lemma continuous_mPay (p : G.player) : Continuous p.mPay := by {
  unfold player.mPay Game.mPay
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro q _
  apply (continuous_apply (s q)).comp
  exact continuous_subtype_val.comp (continuous_apply q)
}

lemma mPay_update_le (p : G.player) (M : G.mStrat) (σ : p.mStrat)
  : p.mPay (update M p σ)
    ≤ univ.sup' univ_nonempty (fun (s : p.pStrat) ↦ p.mPay (update M p s)) := by {
  rw [mPay_update_eq]
  set m := univ.sup' _ (fun (s : p.pStrat) ↦ p.mPay (update M p s))
  apply @le_of_le_of_eq _ _ _ (∑ s : p.pStrat, σ s * m)
  · gcongr with s;
    · exact σ.nonneg s
    simp only [le_sup'_iff, mem_univ, true_and]
    use s
  rw [← sum_mul, σ.sum_coe_eq_one, one_mul]
}

def mPayInc (p : G.player) (M : G.mStrat) (s : p.pStrat) : ℝ
  := max 0 (p.mPay (update M p s) - p.mPay M)

lemma mPayInc_apply (p : G.player) (M : G.mStrat) (s : p.pStrat)
  : p.mPayInc M s = max 0 (p.mPay (update M p s) - p.mPay M) := rfl

lemma mPayInc_nonneg (p : G.player) (M : G.mStrat)
  : ∀ s, p.mPayInc M s ≥ 0 := fun _ ↦ le_max_left 0 _

def min (p : G.player) (M : G.mStrat) : p.pStrat
  := Classical.choose ((PMF.support (M p)).exists_mem_eq_inf' (PMF.support_nonempty (M p)) (fun (s : p.pStrat) ↦ p.mPay (update M p s)))

def min_inf (p : G.player) (M : G.mStrat)
  : p.mPay (update M p (p.min M)) = (PMF.support (M p)).inf' (PMF.support_nonempty (M p)) (fun (s : p.pStrat) ↦ p.mPay (update M p s))
  := (Classical.choose_spec ((PMF.support (M p)).exists_mem_eq_inf' (PMF.support_nonempty (M p)) (fun (s : p.pStrat) ↦ p.mPay (update M p s)))).right.symm

def min_mem_support (p : G.player) (M : G.mStrat)
  : p.min M ∈ PMF.support (M p)
  := (Classical.choose_spec ((PMF.support (M p)).exists_mem_eq_inf' (PMF.support_nonempty (M p)) (fun (s : p.pStrat) ↦ p.mPay (update M p s)))).left

lemma mPay_update_min_le (p : G.player) (M : G.mStrat)
  : p.mPay (update M p (p.min M)) ≤ p.mPay M := by {
  rw [min_inf, mPay_eq]
  set m := (PMF.support (M p)).inf' (PMF.support_nonempty (M p)) (fun (s : p.pStrat) ↦ p.mPay (update M p s))
  apply @le_of_eq_of_le _ _ _ (∑ s : p.pStrat, (M p) s * m)
  · rw [← sum_mul, (M p).sum_coe_eq_one, one_mul]
  apply sum_le_sum
  intro s _
  by_cases ssupp : s ∈ PMF.support (M p)
  · gcongr
    exact (M p).nonneg s
    simp only [inf'_le_iff]
    use s
  simp [PMF.support] at ssupp
  rw [ssupp]
  simp only [zero_mul, le_refl]
}

lemma mPayInc_min_eq_zero (p : G.player) (M : G.mStrat)
  : p.mPayInc M (p.min M) = 0 := by {
  simp only [mPayInc_apply, ge_iff_le, tsub_le_iff_right, zero_add, sub_nonneg, max_eq_left_iff]
  exact p.mPay_update_min_le M
}

lemma continuous_mPayInc (p : G.player) : Continuous p.mPayInc := by {
  unfold mPayInc
  apply continuous_pi
  intro s
  apply continuous_const.max
  apply Continuous.sub _ p.continuous_mPay
  · apply p.continuous_mPay.comp
    exact Continuous.update continuous_id p continuous_const
}

lemma continuous_mPayInc_right (p : G.player) (s : p.pStrat) : Continuous fun M ↦ p.mPayInc M s := by {
  unfold mPayInc
  apply continuous_const.max
  apply Continuous.sub _ p.continuous_mPay
  · apply p.continuous_mPay.comp
    exact Continuous.update continuous_id p continuous_const
}

end player

namespace mStrat

@[ext]
protected lemma ext (M N : G.mStrat) (h : ∀ p, M p = N p) : M = N := funext h

end mStrat

instance : FunLike G.mStratSpace ((p : G.player) × p.pStrat) fun _ ↦ ℝ where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.eq h

lemma mStratSpace_nonneg (Φ : G.mStratSpace) : ∀ v, Φ v ≥ 0 := Φ.2.1

lemma mStratSpace_sum_coe_eq_one (Φ : G.mStratSpace) : ∀ p, ∑ s, Φ ⟨p, s⟩ = 1 := Φ.2.2

def uncurry : G.mStrat ≃ G.mStratSpace where
  toFun M := ⟨fun ⟨p, s⟩ ↦ M p s, ⟨fun ⟨p, s⟩ ↦ (M p).nonneg s, fun p ↦ (M p).sum_coe_eq_one⟩⟩
  invFun F := fun p ↦ ⟨fun s ↦ (F.1 ⟨p, s⟩), ⟨fun s ↦ F.2.left ⟨p, s⟩, F.2.right p⟩⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

abbrev curry : G.mStratSpace → G.mStrat := uncurry.symm

@[simp] lemma uncurry_apply (M : G.mStrat) (v : (p : G.player) × p.pStrat)
  : uncurry M v = M v.1 v.2 := rfl

@[simp] lemma curry_apply (F : G.mStratSpace) (p : G.player) (s : p.pStrat)
  : curry F p s = F ⟨p, s⟩ := rfl

lemma continuous_uncurry : Continuous G.uncurry := by {
  apply Continuous.subtype_mk
  apply continuous_pi
  intro ⟨p, q⟩
  apply (continuous_apply q).comp
  exact continuous_subtype_val.comp (continuous_apply p)
}

lemma continuous_curry : Continuous G.curry := by {
  apply continuous_pi
  intro p
  apply Continuous.subtype_mk
  apply continuous_pi
  intro s
  exact (continuous_apply _).comp continuous_subtype_val
}

namespace pStrat

@[ext]
protected lemma ext (S T : G.pStrat) (h : ∀ p, S p = T p) : S = T := funext h

@[coe] def toMStrat (S : G.pStrat) : G.mStrat
  := fun p ↦ S p

instance : Coe G.pStrat G.mStrat := ⟨toMStrat⟩

@[simp] lemma toMStrat_apply {p : G.player} (S : G.pStrat) (s : p.pStrat)
  : (S : G.mStrat) p s = if s = S p then 1 else 0 := by {
  simp only [toMStrat, (S p).toMStrat_apply]
}

lemma mPay_eq_pPay {p : G.player} (S : G.pStrat) : p.mPay S = p.pPay S := by {
  rw [p.mPay_apply, ← sum_erase_add _ _ (mem_univ S)]
  have : ∑ T in univ.erase S, (∏ q : G.player, ((S : G.mStrat) q (T q))) * (p.pPay T) = 0 := by {
    rw [sum_eq_zero]
    intro T TneS
    simp at TneS
    change T ≠ S at TneS
    obtain ⟨r, TrneSr⟩ := Function.ne_iff.mp TneS
    convert zero_mul (payoff G p T)
    apply prod_eq_zero (mem_univ r)
    simpa
  }
  simp only [this, zero_add, ne_eq]
  convert one_mul (p.pPay S)
  convert prod_const_one with q
  simp only [toMStrat_apply, ite_true]
}

@[simp, norm_cast] lemma coe_update (S : G.pStrat) {p : G.player} {s : p.pStrat}
  : pStrat.toMStrat (update S p s) = update S.toMStrat p s := by {
  ext q
  rw [pStrat.toMStrat]
  by_cases qp : q = p
  · subst qp
    simp only [update_same]
  simp only [update_noteq qp]
  rw [pStrat.toMStrat]
}

lemma mPay_update_pStrat (S : G.pStrat) {p : G.player} {s : p.pStrat}
  : p.mPay (update S.toMStrat p s) = p.pPay (update S p s) := by {
  rw [← mPay_eq_pPay]
  push_cast
  rfl
}

lemma mPay_update (S : G.pStrat) {p : G.player} {σ : p.mStrat}
  : p.mPay (update (S : G.mStrat) p σ) = ∑ T in Finset.filter (fun T : G.pStrat ↦ ∀ q, q ≠ p → T q = S q) univ, σ (T p) * p.pPay T := by {
  let i (s : p.pStrat) (_ : s ∈ univ) : G.pStrat := update S p s
  rw [p.mPay_update_eq, sum_bij i]
  · intro s _
    simp
    intro q qnep
    apply update_noteq qnep
  · intro s _
    simp
    left
    exact mPay_update_pStrat S
  · intro s t _ _ st
    rw [Function.eq_update_iff] at st
    simp at st
    exact st.left
  · intro T Tp
    simp at Tp
    simp
    use T p
    ext q
    by_cases qp : q = p
    · rw [qp, update_same]
    rw [update_noteq qp]
    exact Tp q qp
}

end pStrat

-- Pure best response
def pStrat.IsPBestRe (S : G.pStrat) (p : G.player) : Prop
  := ∀ s : p.pStrat, p.pPay (update S p s) ≤ p.pPay S

-- Pure nash equilibrium
def pStrat.IsPEquil (S : G.pStrat) : Prop
  := ∀ p : G.player, IsPBestRe S p

-- Mixed best response
def mStrat.IsMBestRe (M : G.mStrat) (p : G.player) : Prop
  := ∀ σ : p.mStrat, p.mPay (update M p σ) ≤ p.mPay M

-- Mixed nash equilbrium
def mStrat.IsMEquil (M : G.mStrat) : Prop
  := ∀ p : G.player, IsMBestRe M p

lemma mStrat.isMBestRe_iff (M : G.mStrat) (p : G.player)
  : IsMBestRe M p ↔ ∀ s : p.pStrat,  p.mPay (update M p s) ≤ p.mPay M := by {
  constructor
  · intro h s
    exact h s
  intro h σ
  trans
  · apply p.mPay_update_le
  let upMp (s : p.pStrat) := p.mPay (update M p s)
  obtain ⟨s, ⟨_, sm⟩⟩ := exists_mem_eq_sup' univ_nonempty upMp
  set m := univ.sup' _ upMp
  simp_rw [sm]
  exact h s
}

lemma pStrat.isMEquil_of_isPEquil (S : G.pStrat) (h : IsPEquil S)
  : (S : G.mStrat).IsMEquil := by {
  intro p
  rw [(S : G.mStrat).isMBestRe_iff]
  intro s
  rw [← pStrat.coe_update]
  rw [pStrat.mPay_eq_pPay, pStrat.mPay_eq_pPay]
  exact h p s
}

namespace player

def mStratSimpl (p : G.player) := stdSimplex ℝ p.pStrat

namespace mStratSimpl

@[simp] def mem {p : G.player} {f : p.pStrat → ℝ}
  : f ∈ p.mStratSimpl ↔ (∀ (s : pStrat p), 0 ≤ f s) ∧ ∑ s, f s = 1 := by rfl

def nonneg_of_mem {p : G.player} {f : p.pStrat → ℝ} (h : f ∈ p.mStratSimpl)
  : ∀ s : p.pStrat, f s ≥ 0 := (mem.mp h).left

def sum_one_of_mem {p : G.player} {f : p.pStrat → ℝ} (h : f ∈ p.mStratSimpl)
  : ∑ s, f s = 1 := (mem.mp h).right

def toMStrat {p : G.player} (f : p.pStrat → ℝ) (h : f ∈ p.mStratSimpl)
  : p.mStrat := ⟨f, ⟨nonneg_of_mem h, sum_one_of_mem h⟩⟩

lemma toMStrat_apply {p : G.player} {f : p.pStrat → ℝ} {h : f ∈ p.mStratSimpl} {s : p.pStrat}
  : toMStrat f h s = f s := by {
    simp [toMStrat, FunLike.coe]
}

@[simp] lemma coe_toMStrat_eq_self {p : G.player} (f : p.pStrat → ℝ) (h : f ∈ p.mStratSimpl)
  : (toMStrat f h) = f := by {
  ext s
  exact toMStrat_apply
}

end mStratSimpl

lemma mStrat.mem_mStratSimpl {p : G.player} (σ : p.mStrat)
  : (σ : p.pStrat → ℝ) ∈ p.mStratSimpl := by {
  simp
  exact ⟨σ.nonneg, σ.sum_coe_eq_one⟩
}

lemma range_mStrat (p : G.player) : Set.range (fun σ : p.mStrat ↦ (σ : p.pStrat → ℝ)) = p.mStratSimpl := by {
  ext f
  constructor
  · intro ⟨σ, σf⟩
    rw [← σf]
    exact σ.mem_mStratSimpl
  intro fSimpl
  use mStratSimpl.toMStrat f fSimpl
  simp [mStratSimpl.coe_toMStrat_eq_self f]
}

@[simp] def pStratEmbed (p : G.player) : p.pStrat ↪ (p : G.player) × p.pStrat where
  toFun s := ⟨p, s⟩
  inj' := sigma_mk_injective

def embed (p : G.player) : (p.pStrat → ℝ) →L[ℝ] (p : G.player) × p.pStrat → ℝ where
  toFun f := Function.extend p.pStratEmbed f 0
  map_add' := by {
    intro f g
    simpa using Function.extend_add p.pStratEmbed f g 0 0
  }
  map_smul' := by {
    intro r f
    simpa using Function.extend_smul r p.pStratEmbed f 0
  }
  cont := by {
    simp [extend]
    apply continuous_pi
    intro ⟨q, t⟩
    by_cases pq : p = q
    · have h : ∃ s : p.pStrat, HEq s t := by rw [pq]; use t
      simp [pq, h]
      continuity
    simp [pq]
    continuity
  }

@[simp] lemma embed_apply (p : G.player) (φ : p.pStrat → ℝ) (s : p.pStrat)
  : p.embed φ ⟨p, s⟩ = φ s := by {
  unfold embed
  exact (p.pStratEmbed).injective.extend_apply _ _ s
}

@[simp] lemma embed_apply' {p : G.player} {φ : p.pStrat → ℝ} {q : G.player} (qnep : p ≠ q)
  : ∀ t, p.embed φ ⟨q, t⟩ = 0 := by {
  intro t
  unfold embed
  have h : ¬∃ s, p.pStratEmbed s = ⟨q, t⟩ := by {
    simp [pStratEmbed]
    intro pq
    contradiction
  }
  exact Function.extend_apply' _ _ _ h
}

lemma embed_nonneg_of_nonneg (p : G.player) {φ : p.pStrat → ℝ} (h : ∀ s, φ s ≥ 0)
  : ∀ v, p.embed φ v ≥ 0 := by {
  intro ⟨q, t⟩
  by_cases pq : p = q
  · subst pq
    simp only [embed_apply]
    exact h t
  simp [pq]
}

lemma range_mStrat_embed (p : G.player) : Set.range (fun (σ : p.mStrat) ↦ p.embed σ) = p.embed '' p.mStratSimpl := by {
  rw [← range_mStrat]
  ext Φ
  simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
}

lemma convex_range_mStrat_embed (p : G.player) : Convex ℝ (Set.range (fun (σ : p.mStrat) ↦ p.embed σ)) := by {
  rw [range_mStrat_embed]
  exact Convex.is_linear_image (convex_stdSimplex ℝ p.pStrat) p.embed.isLinear
}

lemma isCompact_range_mStrat_embed (p : G.player) : IsCompact (Set.range (fun (σ : p.mStrat) ↦ p.embed σ)) := by {
  rw [range_mStrat_embed]
  exact IsCompact.image (isCompact_stdSimplex p.pStrat) p.embed.cont
}

end player

lemma mStrat.uncurry_eq_sum_embed (M : G.mStrat)
  : uncurry M = ∑ p : G.player, p.embed (M p) := by {
  ext ⟨q, s⟩
  simp_rw [← Finset.sum_erase_add _ _ (mem_univ q), Pi.add_apply, sum_apply]
  have : ∑ p in univ.erase q, p.embed (M p) ⟨q, s⟩ = 0 := by {
    rw [sum_eq_zero]
    intro p pneq
    simp only [mem_univ, not_true, mem_erase, and_true] at pneq
    simp [p.embed_apply' pneq]
  }
  rw [this, zero_add]
  simp only [uncurry_apply, player.embed_apply]
}

lemma mStratSpace_eq_sum_embed : G.mStratSpace = ∑ p : G.player, Set.range (fun σ : p.mStrat ↦ p.embed σ) := by {
  ext Φ
  constructor
  · intro Φmem
    rw [Set.mem_fintype_sum]
    let M : G.mStrat := curry ⟨Φ, Φmem⟩
    let ι (p : G.player) := p.embed (M p)
    use ι, (by simp)
    exact M.uncurry_eq_sum_embed.symm
  intro Φmem
  rw [Set.mem_fintype_sum] at Φmem
  obtain ⟨f, fran, rfl⟩ := Φmem
  let M : G.mStrat := fun p ↦ Classical.choose (fran p)
  have : ∑  p, f p = uncurry M := by
    rw [M.uncurry_eq_sum_embed]
    congr
    ext p v
    show f p v = (fun σ ↦ p.embed σ) (M p) v
    rw [Classical.choose_spec (fran p)]
  rw [this]
  exact Subtype.mem (uncurry M)
}

lemma mStratSpace_nonempty : Set.Nonempty G.mStratSpace
  := ⟨uncurry default, Subtype.mem (uncurry default)⟩

lemma mStratSpace_convex : Convex ℝ G.mStratSpace := by {
  rw [mStratSpace_eq_sum_embed]
  apply convex_sum
  intro p _
  exact player.convex_range_mStrat_embed p
}

lemma mStratSpace_isCompact : IsCompact G.mStratSpace := by {
  rw [mStratSpace_eq_sum_embed]
  exact compact_sum (fun p ↦ p.isCompact_range_mStrat_embed)
}

lemma isMEquil_iff_mPayInc_zero (M : G.mStrat)
  : M.IsMEquil ↔ ∀ (p : G.player) (s : p.pStrat), p.mPayInc M s = 0 := by {
  constructor
  · intro h
    simp_rw [mStrat.IsMEquil, M.isMBestRe_iff] at h
    intro p s
    simp [player.mPayInc]
    exact h p s
  simp_rw [mStrat.IsMEquil, M.isMBestRe_iff]
  intro h p s
  simp [player.mPayInc] at h
  exact h p s
}

def fpf (G : Game) : G.mStratSpace → G.mStratSpace
  := fun Φ ↦ ⟨fun ⟨p, s⟩ ↦ (Φ ⟨p, s⟩ + p.mPayInc (curry Φ) s)
      / (1 + ∑ t, p.mPayInc (curry Φ) t),
  ⟨by
    intro ⟨p, s⟩
    simp only [ge_iff_le]
    apply div_nonneg
    · exact add_nonneg (Φ.2.1 ⟨p, s⟩) (p.mPayInc_nonneg (curry Φ) s)
    linarith [sum_nonneg fun t _ ↦ p.mPayInc_nonneg (curry Φ) t]
  , by
    intro p
    rw [← Finset.sum_div]
    symm
    apply eq_div_of_mul_eq (by linarith [sum_nonneg fun t _ ↦ p.mPayInc_nonneg (curry Φ) t])
    simp only [one_mul, sum_add_distrib, add_left_inj]
    exact (mStratSpace_sum_coe_eq_one Φ p).symm⟩⟩

lemma continuous_fpf : Continuous G.fpf := by {
  apply Continuous.subtype_mk
  apply continuous_pi
  intro ⟨p, s⟩
  simp only
  apply Continuous.div
  · apply Continuous.add
    · exact (continuous_apply _).comp continuous_subtype_val
    · exact (p.continuous_mPayInc_right s).comp G.continuous_curry
  · apply Continuous.add (continuous_const)
    apply continuous_finset_sum
    intro t _
    exact (p.continuous_mPayInc_right t).comp G.continuous_curry
  intro Φ
  apply ne_of_gt
  calc
    0 < 1 := by norm_num
    _ <= 1 + ∑ t, p.mPayInc (curry Φ) t := by linarith [sum_nonneg fun t _ ↦ p.mPayInc_nonneg (curry Φ) t]
}

lemma mPayInc_eq_zero_of_isFixedPoint (Φ : G.mStratSpace) (h : G.fpf.IsFixedPt Φ)
  : ∀ (p : G.player) (s : p.pStrat), p.mPayInc (curry Φ) s = 0 := by {
  intro p
  let M : G.mStrat := curry Φ
  let m : p.pStrat := p.min M
  have h₁ : Φ ⟨p, m⟩ = (Φ ⟨p, m⟩ + p.mPayInc M m ) / (1 + ∑ t : p.pStrat, p.mPayInc M t) := by
    show Φ ⟨p, m⟩ = G.fpf Φ ⟨p, m⟩
    rw [h.eq]
  rw [p.mPayInc_min_eq_zero, add_zero] at h₁
  have h₂ : 1 + ∑ t : p.pStrat, p.mPayInc M t > 0 := by
    linarith [sum_nonneg (fun t _ ↦ p.mPayInc_nonneg M t)]
  field_simp at h₁
  nth_rw 2 [← mul_one (Φ ⟨p, m⟩)] at h₁
  have h₃ : Φ ⟨p, m⟩ > 0 := by
    apply lt_of_le_of_ne (mStratSpace_nonneg Φ ⟨p, m⟩)
    have := p.min_mem_support (curry Φ)
    simp [PMF.support] at this
    rw [curry_apply] at this
    symm
    exact this
  have h₄ := (mul_left_cancel_iff_of_pos h₃).mp h₁
  nth_rw 2 [← add_zero 1] at h₄
  have h₅ : ∑ t : p.pStrat, p.mPayInc M t = 0 := add_left_cancel h₄
  simp only [mem_univ, (sum_eq_zero_iff_of_nonneg (fun t _ ↦ p.mPayInc_nonneg M t)).mp h₅,
    forall_const]
}

lemma fpf_exists_isFixedPt : ∃ Φ, G.fpf.IsFixedPt Φ
  := brouwer_fixed_point G.mStratSpace mStratSpace_convex mStratSpace_isCompact mStratSpace_nonempty G.fpf continuous_fpf

theorem exists_mStrat_isMEquil : ∃ M : G.mStrat, M.IsMEquil := by {
  obtain ⟨Φ, hΦ⟩ := G.fpf_exists_isFixedPt
  use (curry Φ)
  rw [isMEquil_iff_mPayInc_zero]
  exact mPayInc_eq_zero_of_isFixedPoint Φ hΦ
}

end Game

@[simp] def payoff22 (punishment winner looser reward : ℝ) (p : Bool) (S : (p : Bool) → (fun _ ↦ Bool) p) :=
  match (S p, S !p) with
  | (false, false) => punishment
  | (true, false) => winner
  | (false, true) => looser
  | (true, true) => reward

/-  Two player game. Each player has exactly two strategies. -/
def Game22 (punishment winner looser reward : ℝ) : Game where
  player := Bool
  player_finite := Bool.fintype
  strategy := fun _ ↦ Bool
  strategy_finite := fun _ ↦ Bool.fintype
  strategy_inhabited := fun _ ↦ ⟨true⟩
  payoff := payoff22 punishment winner looser reward

namespace Game22

@[simp] lemma payoff_eq_payoff22 {punishment winner looser reward : ℝ}
  : (Game22 punishment winner looser reward ).payoff = payoff22 punishment winner looser reward := rfl


open Game
variable {a b c d : ℝ}

def none : Π p : (Game22 a b c d).player, p.pStrat
| _ => false

def first : Π p : (Game22 a b c d).player, p.pStrat := id

def second : Π p : (Game22 a b c d).player, p.pStrat := not

def both : Π p : (Game22 a b c d).player, p.pStrat
| _ => true

/- Chicken game
See: https://en.wikipedia.org/wiki/Chicken_(game)
Strategies swerve, encoded as false, and straight, encoded as true. -/
def Chicken := Game22 0 1 (-1) (-1000)

example : @Game.pStrat.IsPEquil Chicken first:= by {
  intro p s
  cases p
  <;> simp [Chicken, first, player.pPay, pPay]
  <;> cases s
  <;> norm_num
}

example : @Game.pStrat.IsPEquil Chicken second := by {
  intro p s
  cases p
  <;> simp [Chicken, second, player.pPay, pPay]
  <;> cases s
  <;> norm_num
}

/- Prisoner's dilemma
See: https://en.wikipedia.org/wiki/Prisoner%27s_dilemma
Strategies defect, encoded as false, and cooperate, encoded as true. -/
def PrisonersDilemma := Game22 2 0 3 1

example : @Game.pStrat.IsPEquil PrisonersDilemma none := by {
 intro p s
 cases p
 <;> simp [PrisonersDilemma, none, player.pPay, pPay]
 <;> cases s
 <;> norm_num
}

end Game22

end
