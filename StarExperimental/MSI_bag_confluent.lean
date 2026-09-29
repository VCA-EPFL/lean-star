import StarExperimental.MSI_bag_shape
import StarExperimental.SumListLemmas

/-! # `MSI_bag_confluent`: diamante e commutazione di ARS per il modello bag, senza invarianti

Le due ipotesi di `ReachingStar.trace_inclusion` che riguardano gli stati raggiungibili:
* `msi_confluent`: due riduzioni interne da uno stato raggiungibile si ricongiungono;
* `msi_commutes_upto`: un passo esterno e una riduzione interna si ricongiungono a meno di passi
  interni.

Che cosa si usa sugli stati raggiungibili:
* **le viste** (`noBad_of_reach`, il risultato della tattica backward sui 15 pattern, passi interni
  ed esterni) e `synced` (l'`Inv` del setup della tattica). Da queste, per sola lettura, i fatti
  strutturali `NoBadFacts` (righe ⇔ token, esclusione): non sono un invariante dimostrato a mano,
  sono i pattern letti sullo stato (`noBadFacts_of_good`);
* **il valore logico** `val x`: il valore dell'unico token `M` in giro, se c'è, altrimenti quello
  del parent. È una *funzione* dello stato, ben definita grazie alle viste (`lvm_exists`,
  `lvm_unique`); l'unico fatto sui valori è che i passi interni non la cambiano (`val_step`),
  perché copiano valori e non ne inventano;
* per `msi_commutes_upto` soltanto: `SVal`, "le copie `S` e i grant `rsS` portano il valore del
  parent". Questo è davvero un invariante (le viste non hanno valori) ed è necessario: senza, una
  load servita da una copia `S` con un valore diverso da quello del parent non commuta con il
  rilascio di quella copia. È l'unico invariante del file.

Il ricongiungimento è lo *stato canonico* `canon x (val x)`: tutte le cache in `I` con valore
`val x`, code vuote, righe a `I`, parent a `val x`, `extqueue` di `x`. Ci si arriva con le
misure `μ1` (cache non in `I`, grant, rilasci), `μ2` (richieste), `μ3` (invalidate stantii),
`μ4` (cache con valore diverso). -/

open THEORY Relation
open ReachingStar (trans_refl)

namespace MSIBag

variable {n : Nat}

/-! ## Predicati sui messaggi e token -/

def isGrant : PCEvent → Bool
  | .rsM _ => true
  | .rsS _ => true
  | _ => false

def isInval : PCEvent → Bool
  | .rqIμ => true
  | .rqIσ => true
  | _ => false

def isRelease : CPEvent → Bool
  | .rsIμ _ => true
  | .rsIσ => true
  | _ => false

def isRequest : CPEvent → Bool
  | .rqS => true
  | .rqM => true
  | _ => false

/-- Token `M` di una cache: stato `M`, grant `rsM` in volo, rilasci `rsIμ` in volo. -/
def mtokC (c : CacheState) : Nat :=
  (if c.state = Bstate.M then 1 else 0) + c.queue_pc.countP (fun e => isGrantM e = true)
    + c.queue_cp.countP (fun e => isReleaseM e = true)

/-- Token `S` di una cache: stato `S`, grant `rsS` in volo, rilasci `rsIσ` in volo. -/
def stokC (c : CacheState) : Nat :=
  (if c.state = Bstate.S then 1 else 0) + c.queue_pc.countP (fun e => isGrantS e = true)
    + c.queue_cp.countP (fun e => isReleaseS e = true)

def mtok (x : MSIState n) (k : Fin n) : Nat := mtokC (x.caches k)
def stok (x : MSIState n) (k : Fin n) : Nat := stokC (x.caches k)

/-! ## I fatti strutturali letti dalle viste -/

/-- Ciò che i 15 pattern dicono di uno stato senza viste cattive (con `synced`). Non è un
invariante: è `noBad_of_reach` riscritto in termini di righe e token (`noBadFacts_of_good`). -/
structure NoBadFacts (x : MSIState n) : Prop where
  synced : synced x
  rowM : ∀ k, x.parent.shared_state k = Bstate.M → mtok x k = 1 ∧ stok x k = 0
  rowS : ∀ k, x.parent.shared_state k = Bstate.S → stok x k = 1 ∧ mtok x k = 0
  rowI : ∀ k, x.parent.shared_state k = Bstate.I → mtok x k = 0 ∧ stok x k = 0
  excl : ∀ k k', x.parent.shared_state k = Bstate.M → k' ≠ k → x.parent.shared_state k' = Bstate.I
  cacheM : ∀ k, (x.caches k).state = Bstate.M → x.parent.shared_state k = Bstate.M
  cacheS : ∀ k, (x.caches k).state = Bstate.S → x.parent.shared_state k = Bstate.S

/-- Con `synced`, i contatori del parent sono quelli della cache. -/
theorem muMsgs_eq {x : MSIState n} (hs : synced x) (k : Fin n) :
    muMsgs x.parent k = (x.caches k).queue_pc.countP (fun e => isGrantM e = true)
      + (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) := by
  obtain ⟨h1, h2⟩ := hs k
  unfold muMsgs
  rw [h1, h2]

theorem sigMsgs_eq {x : MSIState n} (hs : synced x) (k : Fin n) :
    sigMsgs x.parent k = (x.caches k).queue_pc.countP (fun e => isGrantS e = true)
      + (x.caches k).queue_cp.countP (fun e => isReleaseS e = true) := by
  obtain ⟨h1, h2⟩ := hs k
  unfold sigMsgs
  rw [h1, h2]

/-- La vista `(k, k)` (`eq = true`), letta su righe e token. -/
theorem noBadFacts_of_noBad_aux1 {c d : Bstate} {mu sg : Nat}
    (h : ¬ badView ⟨c, d, d, BackwardGen.Cnt.ofCount mu, BackwardGen.Cnt.ofCount sg, true⟩) :
    (d = Bstate.M → (if c = Bstate.M then 1 else 0) + mu = 1 ∧ (if c = Bstate.S then 1 else 0) + sg = 0)
    ∧ (d = Bstate.S → (if c = Bstate.S then 1 else 0) + sg = 1 ∧ (if c = Bstate.M then 1 else 0) + mu = 0)
    ∧ (d = Bstate.I → (if c = Bstate.M then 1 else 0) + mu = 0 ∧ (if c = Bstate.S then 1 else 0) + sg = 0)
    ∧ (c = Bstate.M → d = Bstate.M) ∧ (c = Bstate.S → d = Bstate.S) := by
  rcases BackwardGen.Cnt.ofCount_cases mu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ <;>
  rcases BackwardGen.Cnt.ofCount_cases sg with ⟨h3, rfl⟩ | ⟨h3, rfl⟩ | ⟨h3, -⟩ <;>
  cases c <;> cases d <;> simp [badView, h1, h3] at h ⊢

/-- La vista `(k, k')` con `k ≠ k'` (`eq = false`): riga `M` di `k` ⇒ riga `I` di `k'`. -/
theorem noBadFacts_of_noBad_aux2 {c d d' : Bstate} {mu sg : Nat}
    (h : ¬ badView ⟨c, d, d', BackwardGen.Cnt.ofCount mu, BackwardGen.Cnt.ofCount sg, false⟩) (hd : d = Bstate.M) :
    d' = Bstate.I := by
  subst hd
  by_contra hne
  apply h
  unfold badView
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hne⟩)))))))

/-- **Le viste, lette sullo stato.** -/
theorem noBadFacts_of_noBad {x : MSIState n} (hs : synced x)
    (hb : ∀ i j, ¬ badView (msiView x i j)) : NoBadFacts x := by
  have hm : ∀ k, mtok x k = (if (x.caches k).state = Bstate.M then 1 else 0) + muMsgs x.parent k := by
    intro k
    unfold mtok mtokC
    rw [muMsgs_eq hs k, Nat.add_assoc]
  have hsg : ∀ k, stok x k = (if (x.caches k).state = Bstate.S then 1 else 0) + sigMsgs x.parent k := by
    intro k
    unfold stok stokC
    rw [sigMsgs_eq hs k, Nat.add_assoc]
  have hkk : ∀ k, ¬ badView ⟨(x.caches k).state, x.parent.shared_state k, x.parent.shared_state k,
      BackwardGen.Cnt.ofCount (muMsgs x.parent k), BackwardGen.Cnt.ofCount (sigMsgs x.parent k), true⟩ := by
    intro k
    have h := hb k k
    unfold msiView at h
    rw [decide_eq_true (rfl : k = k)] at h
    exact h
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hm k, hsg k]
    exact (noBadFacts_of_noBad_aux1 (hkk k)).1 hk
  · intro k hk
    rw [hsg k, hm k]
    exact (noBadFacts_of_noBad_aux1 (hkk k)).2.1 hk
  · intro k hk
    rw [hm k, hsg k]
    exact (noBadFacts_of_noBad_aux1 (hkk k)).2.2.1 hk
  · intro k k' hk hne
    have h := hb k k'
    have hd : decide (k = k') = false := decide_eq_false (fun h => hne h.symm)
    unfold msiView at h
    rw [hd] at h
    exact noBadFacts_of_noBad_aux2 h hk
  · intro k hk
    exact (noBadFacts_of_noBad_aux1 (hkk k)).2.2.2.1 hk
  · intro k hk
    exact (noBadFacts_of_noBad_aux1 (hkk k)).2.2.2.2 hk

theorem noBadFacts_of_good {x : MSIState n} (hx : Good x) : NoBadFacts x :=
  noBadFacts_of_noBad (synced_of_good hx) (noBad_of_good hx)

theorem noBadFacts_of_reach {x : MSIState n} (hx : Reach x) : NoBadFacts x :=
  noBadFacts_of_good (good_of_reach hx)

/-! ## Lemmi sui token -/

theorem mtok_one_cases {x : MSIState n} {k : Fin n} (h : mtok x k = 1) :
    ((x.caches k).state = Bstate.M ∧ (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 0
        ∧ (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) = 0)
    ∨ ((x.caches k).state ≠ Bstate.M ∧ (∃ v, PCEvent.rsM v ∈ (x.caches k).queue_pc)
        ∧ (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) = 0)
    ∨ ((x.caches k).state ≠ Bstate.M ∧ (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 0
        ∧ (∃ v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp)) := by
  unfold mtok mtokC at h
  by_cases hM : (x.caches k).state = Bstate.M
  · rw [if_pos hM] at h
    exact Or.inl ⟨hM, by omega, by omega⟩
  · rw [if_neg hM] at h
    by_cases hg : (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 0
    · have hpos : 0 < (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) := by omega
      obtain ⟨m, hm, hp⟩ := Multiset.countP_pos.mp hpos
      refine Or.inr (Or.inr ⟨hM, hg, ?_⟩)
      cases m with
      | rsIμ v => exact ⟨v, hm⟩
      | rsIσ => simp [isReleaseM] at hp
      | rqS => simp [isReleaseM] at hp
      | rqM => simp [isReleaseM] at hp
    · have hpos : 0 < (x.caches k).queue_pc.countP (fun e => isGrantM e = true) :=
        Nat.pos_of_ne_zero hg
      obtain ⟨m, hm, hp⟩ := Multiset.countP_pos.mp hpos
      refine Or.inr (Or.inl ⟨hM, ?_, by omega⟩)
      cases m with
      | rsM v => exact ⟨v, hm⟩
      | rsS v => simp [isGrantM] at hp
      | rqIμ => simp [isGrantM] at hp
      | rqIσ => simp [isGrantM] at hp

theorem mtok_zero_facts {x : MSIState n} {k : Fin n} (h : mtok x k = 0) :
    (x.caches k).state ≠ Bstate.M ∧ (∀ v, PCEvent.rsM v ∉ (x.caches k).queue_pc)
      ∧ (∀ v, CPEvent.rsIμ v ∉ (x.caches k).queue_cp) := by
  unfold mtok mtokC at h
  refine ⟨?_, ?_, ?_⟩
  · intro hM
    rw [if_pos hM] at h
    omega
  · intro v hv
    have hg : (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 0 := by omega
    exact Multiset.countP_eq_zero.mp hg _ hv rfl
  · intro v hv
    have hr : (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) = 0 := by omega
    exact Multiset.countP_eq_zero.mp hr _ hv rfl

theorem stok_zero_facts {x : MSIState n} {k : Fin n} (h : stok x k = 0) :
    (x.caches k).state ≠ Bstate.S ∧ (∀ v, PCEvent.rsS v ∉ (x.caches k).queue_pc)
      ∧ CPEvent.rsIσ ∉ (x.caches k).queue_cp := by
  unfold stok stokC at h
  refine ⟨?_, ?_, ?_⟩
  · intro hS
    rw [if_pos hS] at h
    omega
  · intro v hv
    have hg : (x.caches k).queue_pc.countP (fun e => isGrantS e = true) = 0 := by omega
    exact Multiset.countP_eq_zero.mp hg _ hv rfl
  · intro hv
    have hr : (x.caches k).queue_cp.countP (fun e => isReleaseS e = true) = 0 := by omega
    exact Multiset.countP_eq_zero.mp hr _ hv rfl

theorem stok_one_cases {x : MSIState n} {k : Fin n} (h : stok x k = 1) :
    ((x.caches k).state = Bstate.S ∧ (x.caches k).queue_pc.countP (fun e => isGrantS e = true) = 0
        ∧ (x.caches k).queue_cp.countP (fun e => isReleaseS e = true) = 0)
    ∨ ((x.caches k).state ≠ Bstate.S ∧ (∃ v, PCEvent.rsS v ∈ (x.caches k).queue_pc)
        ∧ (x.caches k).queue_cp.countP (fun e => isReleaseS e = true) = 0)
    ∨ ((x.caches k).state ≠ Bstate.S ∧ (x.caches k).queue_pc.countP (fun e => isGrantS e = true) = 0
        ∧ CPEvent.rsIσ ∈ (x.caches k).queue_cp) := by
  unfold stok stokC at h
  by_cases hS : (x.caches k).state = Bstate.S
  · rw [if_pos hS] at h
    exact Or.inl ⟨hS, by omega, by omega⟩
  · rw [if_neg hS] at h
    by_cases hg : (x.caches k).queue_pc.countP (fun e => isGrantS e = true) = 0
    · have hpos : 0 < (x.caches k).queue_cp.countP (fun e => isReleaseS e = true) := by omega
      obtain ⟨m, hm, hp⟩ := Multiset.countP_pos.mp hpos
      refine Or.inr (Or.inr ⟨hS, hg, ?_⟩)
      cases m with
      | rsIσ => exact hm
      | rsIμ v => simp [isReleaseS] at hp
      | rqS => simp [isReleaseS] at hp
      | rqM => simp [isReleaseS] at hp
    · have hpos : 0 < (x.caches k).queue_pc.countP (fun e => isGrantS e = true) :=
        Nat.pos_of_ne_zero hg
      obtain ⟨m, hm, hp⟩ := Multiset.countP_pos.mp hpos
      refine Or.inr (Or.inl ⟨hS, ?_, by omega⟩)
      cases m with
      | rsS v => exact ⟨v, hm⟩
      | rsM v => simp [isGrantS] at hp
      | rqIμ => simp [isGrantS] at hp
      | rqIσ => simp [isGrantS] at hp

/-- Al più un token `M` in tutto il sistema: le righe `M` sono al più una. -/
theorem mtok_global {x : MSIState n} (hf : NoBadFacts x) {k k' : Fin n}
    (hk : mtok x k = 1) (hk' : mtok x k' = 1) : k = k' := by
  have rowM : ∀ j, mtok x j = 1 → x.parent.shared_state j = Bstate.M := by
    intro j hj
    cases hrow : x.parent.shared_state j with
    | M => rfl
    | I => have := (hf.rowI j hrow).1; omega
    | S => have := (hf.rowS j hrow).2; omega
  by_contra hne
  have h1 := rowM k hk
  have h2 := rowM k' hk'
  have h3 := hf.excl k k' h1 (Ne.symm hne)
  rw [h3] at h2
  cases h2

theorem mtok_le_one {x : MSIState n} (hf : NoBadFacts x) (k : Fin n) : mtok x k ≤ 1 := by
  cases hrow : x.parent.shared_state k with
  | M => have := (hf.rowM k hrow).1; omega
  | I => have := (hf.rowI k hrow).1; omega
  | S => have := (hf.rowS k hrow).2; omega

/-! ## Il valore logico -/

/-- La specifica di `val`: `m` è il valore di ogni token `M` in giro, e del parent quando non
ce ne sono. Non è un invariante: esiste ed è unico in ogni stato senza viste cattive. -/
structure LVM (x : MSIState n) (m : Value) : Prop where
  cacheM : ∀ k, (x.caches k).state = Bstate.M → (x.caches k).value = m
  grantM : ∀ k v, PCEvent.rsM v ∈ (x.caches k).queue_pc → v = m
  release : ∀ k v, CPEvent.rsIμ v ∈ (x.caches k).queue_cp → v = m
  parent : (∀ k, mtok x k = 0) → x.parent.value = m

/-- Se `k` porta il token `M`, ogni altro indice non ne ha. -/
theorem lvm_exists_aux1 {x : MSIState n} (hf : NoBadFacts x) {k : Fin n} (hk : mtok x k = 1)
    {k' : Fin n} (hne : k' ≠ k) : mtok x k' = 0 := by
  have hle := mtok_le_one hf k'
  by_contra h0
  have h1 : mtok x k' = 1 := by omega
  exact hne (mtok_global hf hk h1).symm

/-- In un multiset con `countP p = 1` due elementi che soddisfano `p` coincidono. -/
theorem lvm_exists_aux2 {α : Type} [DecidableEq α] {s : Multiset α} {p : α → Prop}
    [DecidablePred p] (h : s.countP p = 1) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hpa : p a) (hpb : p b) : a = b := by
  by_contra hab
  have hb' : b ∈ s.erase a := (Multiset.mem_erase_of_ne (fun h => hab h.symm)).mpr hb
  have h2 : (a ::ₘ s.erase a).countP p = 1 := by rwa [Multiset.cons_erase ha]
  rw [Multiset.countP_cons, if_pos hpa] at h2
  have h3 : (s.erase a).countP p = 0 := by omega
  exact (Multiset.countP_eq_zero.mp h3) b hb' hpb

/-- Se nessun indice ha `mtok = 1`, tutti hanno `mtok = 0`. -/
theorem lvm_exists_aux3 {x : MSIState n} (hf : NoBadFacts x) (h : ¬ ∃ k, mtok x k = 1)
    (k : Fin n) : mtok x k = 0 := by
  have hle := mtok_le_one hf k
  by_contra h0
  exact h ⟨k, by omega⟩

theorem lvm_exists {x : MSIState n} (hf : NoBadFacts x) : ∃ m, LVM x m := by
  by_cases hex : ∃ k, mtok x k = 1
  · obtain ⟨k, hk⟩ := hex
    have hoth : ∀ k', k' ≠ k → mtok x k' = 0 := fun k' hne => lvm_exists_aux1 hf hk hne
    rcases mtok_one_cases hk with ⟨hM, hg, hr⟩ | ⟨hM, ⟨v, hv⟩, hr⟩ | ⟨hM, hg, ⟨v, hv⟩⟩
    · refine ⟨(x.caches k).value, ?_, ?_, ?_, ?_⟩
      · intro k' hk'
        by_cases hne : k' = k
        · subst hne; rfl
        · exact absurd hk' (mtok_zero_facts (hoth k' hne)).1
      · intro k' v hv
        by_cases hne : k' = k
        · subst hne
          exact absurd rfl (Multiset.countP_eq_zero.mp hg _ hv)
        · exact absurd hv ((mtok_zero_facts (hoth k' hne)).2.1 v)
      · intro k' v hv
        by_cases hne : k' = k
        · subst hne
          exact absurd rfl (Multiset.countP_eq_zero.mp hr _ hv)
        · exact absurd hv ((mtok_zero_facts (hoth k' hne)).2.2 v)
      · intro h0
        have := h0 k
        omega
    · have hg1 : (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 1 := by
        unfold mtok mtokC at hk
        rw [if_neg hM, hr] at hk
        omega
      refine ⟨v, ?_, ?_, ?_, ?_⟩
      · intro k' hk'
        by_cases hne : k' = k
        · subst hne
          exact absurd hk' hM
        · exact absurd hk' (mtok_zero_facts (hoth k' hne)).1
      · intro k' v' hv'
        by_cases hne : k' = k
        · subst hne
          have := lvm_exists_aux2 hg1 hv' hv rfl rfl
          exact PCEvent.rsM.inj this
        · exact absurd hv' ((mtok_zero_facts (hoth k' hne)).2.1 v')
      · intro k' v' hv'
        by_cases hne : k' = k
        · subst hne
          exact absurd rfl (Multiset.countP_eq_zero.mp hr _ hv')
        · exact absurd hv' ((mtok_zero_facts (hoth k' hne)).2.2 v')
      · intro h0
        have := h0 k
        omega
    · have hr1 : (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) = 1 := by
        unfold mtok mtokC at hk
        rw [if_neg hM, hg] at hk
        omega
      refine ⟨v, ?_, ?_, ?_, ?_⟩
      · intro k' hk'
        by_cases hne : k' = k
        · subst hne
          exact absurd hk' hM
        · exact absurd hk' (mtok_zero_facts (hoth k' hne)).1
      · intro k' v' hv'
        by_cases hne : k' = k
        · subst hne
          exact absurd rfl (Multiset.countP_eq_zero.mp hg _ hv')
        · exact absurd hv' ((mtok_zero_facts (hoth k' hne)).2.1 v')
      · intro k' v' hv'
        by_cases hne : k' = k
        · subst hne
          have := lvm_exists_aux2 hr1 hv' hv rfl rfl
          exact CPEvent.rsIμ.inj this
        · exact absurd hv' ((mtok_zero_facts (hoth k' hne)).2.2 v')
      · intro h0
        have := h0 k
        omega
  · have h0 : ∀ k, mtok x k = 0 := lvm_exists_aux3 hf hex
    refine ⟨x.parent.value, ?_, ?_, ?_, ?_⟩
    · intro k hk
      exact absurd hk (mtok_zero_facts (h0 k)).1
    · intro k v hv
      exact absurd hv ((mtok_zero_facts (h0 k)).2.1 v)
    · intro k v hv
      exact absurd hv ((mtok_zero_facts (h0 k)).2.2 v)
    · intro _
      rfl

theorem lvm_unique {x : MSIState n} {m m' : Value} (hf : NoBadFacts x) (h : LVM x m) (h' : LVM x m') :
    m = m' := by
  by_cases hex : ∃ k, mtok x k = 1
  · obtain ⟨k, hk⟩ := hex
    rcases mtok_one_cases hk with ⟨hM, _, _⟩ | ⟨_, ⟨v, hv⟩, _⟩ | ⟨_, _, ⟨v, hv⟩⟩
    · rw [← h.cacheM k hM, ← h'.cacheM k hM]
    · rw [← h.grantM k v hv, ← h'.grantM k v hv]
    · rw [← h.release k v hv, ← h'.release k v hv]
  · have h0 : ∀ k, mtok x k = 0 := lvm_exists_aux3 hf hex
    rw [← h.parent h0, ← h'.parent h0]

open Classical in
/-- Il valore logico. -/
noncomputable def val (x : MSIState n) : Value :=
  if h : ∃ m, LVM x m then Classical.choose h else 0

theorem lvm_val {x : MSIState n} (hf : NoBadFacts x) : LVM x (val x) := by
  unfold val
  rw [dif_pos (lvm_exists hf)]
  exact Classical.choose_spec (lvm_exists hf)

theorem val_eq_of_lvm {x : MSIState n} {m : Value} (hf : NoBadFacts x) (h : LVM x m) : val x = m :=
  lvm_unique hf (lvm_val hf) h

/-- `countP` dei grant `M` dopo un `cons` di un messaggio che non è un grant `M`. -/
theorem lvm_step_aux1 {s : Multiset PCEvent} (a : PCEvent) (ha : isGrantM a = false) :
    (a ::ₘ s).countP (fun e => isGrantM e = true) = s.countP (fun e => isGrantM e = true) := by
  rw [Multiset.countP_cons, ha]
  simp

/-- `countP` dei rilasci `M` dopo un `erase` di un messaggio che non è un rilascio `M`. -/
theorem lvm_step_aux2 {s : Multiset CPEvent} {a : CPEvent} (h : a ∈ s) (ha : isReleaseM a = false) :
    (s.erase a).countP (fun e => isReleaseM e = true) = s.countP (fun e => isReleaseM e = true) := by
  have h1 := countP_erase_releaseM h
  rw [ha] at h1
  simpa using h1

/-- Un passo interno della cache non cambia i suoi token `M`. -/
theorem lvm_step_aux3 {s1 c' : CacheState} {e : CacheInternalEvent}
    (h : cache_msi_step_internal s1 e c') : mtokC c' = mtokC s1 := by
  cases h with
  | rq_data_not_available hM =>
    have e1 : isReleaseM (CPEvent.rsIμ s1.value) = true := rfl
    unfold mtokC
    simp [hM, e1]
    omega
  | rq_data_not_available1 hS =>
    have e1 : isReleaseM CPEvent.rsIσ = false := rfl
    unfold mtokC
    simp [hS, e1]
  | upgrade_from_I_rq hI =>
    have e1 : isReleaseM CPEvent.rqM = false := rfl
    unfold mtokC
    simp [hI, e1]
  | upgrade_from_I_rq1 hI =>
    have e1 : isReleaseM CPEvent.rqS = false := rfl
    unfold mtokC
    simp [hI, e1]
  | upgrade_from_I_rs v hmem hI =>
    have h1 : (s1.queue_pc.erase (PCEvent.rsM v)).countP (fun e => isGrantM e = true) + 1
        = s1.queue_pc.countP (fun e => isGrantM e = true) := countP_erase_grantM hmem
    unfold mtokC
    simp [hI]
    omega
  | upgrade_from_I_rsS v hmem hI =>
    have h1 : (s1.queue_pc.erase (PCEvent.rsS v)).countP (fun e => isGrantM e = true) + 0
        = s1.queue_pc.countP (fun e => isGrantM e = true) := countP_erase_grantM hmem
    unfold mtokC
    simp [hI]
    omega
  | downgrade_from_M_rs hmem hM =>
    have h1 : (s1.queue_pc.erase PCEvent.rqIμ).countP (fun e => isGrantM e = true) + 0
        = s1.queue_pc.countP (fun e => isGrantM e = true) := countP_erase_grantM hmem
    have e1 : isReleaseM (CPEvent.rsIμ s1.value) = true := rfl
    unfold mtokC
    simp [hM, e1]
    omega
  | downgrade_from_M_rs1 hmem hS =>
    have h1 : (s1.queue_pc.erase PCEvent.rqIσ).countP (fun e => isGrantM e = true) + 0
        = s1.queue_pc.countP (fun e => isGrantM e = true) := countP_erase_grantM hmem
    have e1 : isReleaseM CPEvent.rsIσ = false := rfl
    unfold mtokC
    simp [hS, e1]
    omega

/-- I fatti di `LVM` sulla cache dopo un suo passo interno, da quelli prima. -/
theorem lvm_step_aux4 {s1 c' : CacheState} {e : CacheInternalEvent} {m : Value}
    (h : cache_msi_step_internal s1 e c')
    (hcM : s1.state = Bstate.M → s1.value = m)
    (hgM : ∀ v, PCEvent.rsM v ∈ s1.queue_pc → v = m)
    (hrel : ∀ v, CPEvent.rsIμ v ∈ s1.queue_cp → v = m) :
    (c'.state = Bstate.M → c'.value = m)
    ∧ (∀ v, PCEvent.rsM v ∈ c'.queue_pc → v = m)
    ∧ (∀ v, CPEvent.rsIμ v ∈ c'.queue_cp → v = m) := by
  cases h with
  | rq_data_not_available hM =>
    refine ⟨fun h => Bstate.noConfusion h, hgM, ?_⟩
    intro v hv
    rcases Multiset.mem_cons.1 hv with h | h
    · rw [CPEvent.rsIμ.inj h]; exact hcM hM
    · exact hrel v h
  | rq_data_not_available1 hS =>
    refine ⟨fun h => Bstate.noConfusion h, hgM, ?_⟩
    intro v hv
    rcases Multiset.mem_cons.1 hv with h | h
    · exact CPEvent.noConfusion h
    · exact hrel v h
  | upgrade_from_I_rq hI =>
    refine ⟨fun h => Bstate.noConfusion (hI.symm.trans h), hgM, ?_⟩
    intro v hv
    rcases Multiset.mem_cons.1 hv with h | h
    · exact CPEvent.noConfusion h
    · exact hrel v h
  | upgrade_from_I_rq1 hI =>
    refine ⟨fun h => Bstate.noConfusion (hI.symm.trans h), hgM, ?_⟩
    intro v hv
    rcases Multiset.mem_cons.1 hv with h | h
    · exact CPEvent.noConfusion h
    · exact hrel v h
  | upgrade_from_I_rs v hmem hI =>
    refine ⟨fun _ => hgM v hmem, ?_, hrel⟩
    intro v' hv
    exact hgM v' (Multiset.mem_of_mem_erase hv)
  | upgrade_from_I_rsS v hmem hI =>
    refine ⟨fun h => Bstate.noConfusion h, ?_, hrel⟩
    intro v' hv
    exact hgM v' (Multiset.mem_of_mem_erase hv)
  | downgrade_from_M_rs hmem hM =>
    refine ⟨fun h => Bstate.noConfusion h, ?_, ?_⟩
    · intro v' hv
      exact hgM v' (Multiset.mem_of_mem_erase hv)
    · intro v hv
      rcases Multiset.mem_cons.1 hv with h | h
      · rw [CPEvent.rsIμ.inj h]; exact hcM hM
      · exact hrel v h
  | downgrade_from_M_rs1 hmem hS =>
    refine ⟨fun h => Bstate.noConfusion h, ?_, ?_⟩
    · intro v' hv
      exact hgM v' (Multiset.mem_of_mem_erase hv)
    · intro v hv
      rcases Multiset.mem_cons.1 hv with h | h
      · exact CPEvent.noConfusion h
      · exact hrel v h

/-- `LVM` dopo un passo della cache `k`, dai fatti sulla nuova cache. -/
theorem lvm_step_aux5 {x : MSIState n} {m : Value} {k : Fin n} {c' : CacheState}
    (hl : LVM x m)
    (hcM : c'.state = Bstate.M → c'.value = m)
    (hgM : ∀ v, PCEvent.rsM v ∈ c'.queue_pc → v = m)
    (hrel : ∀ v, CPEvent.rsIμ v ∈ c'.queue_cp → v = m)
    (htok : mtokC c' = mtokC (x.caches k)) :
    LVM { x with caches := update_Fin k c' x.caches,
                 parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                 parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } m := by
  obtain ⟨hcM0, hgM0, hrel0, hpar0⟩ := hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hcM hk'
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcM0 _ hk'
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact hgM v hv
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hgM0 _ v hv
  · intro k' v hv
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hv
      exact hrel v hv
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hv
      exact hrel0 _ v hv
  · intro hall
    show x.parent.value = m
    apply hpar0
    intro k'
    have hk0 := hall k'
    unfold mtok at hk0 ⊢
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk0
      rw [← htok]
      exact hk0
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk0
      exact hk0

/-- `LVM` dopo un passo del parent sull'indice `k`, dai fatti sulle nuove code di `k`. -/
theorem lvm_step_aux6 {x : MSIState n} {m : Value} {k : Fin n} {p' : ParentState n}
    (hl : LVM x m)
    (hgM : ∀ v, PCEvent.rsM v ∈ p'.queue_pci k → v = m)
    (hrel : ∀ v, CPEvent.rsIμ v ∈ p'.queue_cip k → v = m)
    (hpar : (∀ k', mtok { x with
                caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } k' = 0) → p'.value = m) :
    LVM { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                 parent := p' } m := by
  obtain ⟨hcM0, hgM0, hrel0, _⟩ := hl
  refine ⟨?_, ?_, ?_, hpar⟩
  · intro k' hk'
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hk' ⊢
      exact hcM0 _ hk'
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hk' ⊢
      exact hcM0 k' hk'
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hgM v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hgM0 k' v hmem
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      exact hrel v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hrel0 k' v hmem

/-- Se i token `M` di `k` nelle copie lato parent non cambiano, "nessun token `M`" dopo il passo
dà "nessun token `M`" prima. -/
theorem lvm_step_aux7 {x : MSIState n} {k : Fin n} {p' : ParentState n}
    (hM : (p'.queue_pci k).countP (fun e => isGrantM e = true)
            = (x.caches k).queue_pc.countP (fun e => isGrantM e = true))
    (hR : (p'.queue_cip k).countP (fun e => isReleaseM e = true)
            = (x.caches k).queue_cp.countP (fun e => isReleaseM e = true))
    (h0 : ∀ k', mtok { x with
                caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                parent := p' } k' = 0) :
    ∀ k', mtok x k' = 0 := by
  intro k'
  have this := h0 k'
  by_cases hk : k' = k
  · subst hk
    unfold mtok mtokC at this ⊢
    simp only [update_Fin_gss] at this
    rw [hM, hR] at this
    exact this
  · unfold mtok at this ⊢
    simp only [update_Fin_gso2 _ _ _ _ hk] at this
    exact this

/-- Il caso parent di `lvm_step`. -/
theorem lvm_step_aux8 {x : MSIState n} {m : Value} {k : Fin n} {e : ParentUpdQueueInternalEvent n}
    {p' : ParentState n} (hf : NoBadFacts x) (hl : LVM x m)
    (h : parent_msi_step x.parent (.upd_queue e k) p') :
    LVM { x with caches := update_Fin k { x.caches k with queue_cp := p'.queue_cip k,
                                                          queue_pc := p'.queue_pci k } x.caches,
                 parent := p' } m := by
  have hcp := (hf.synced k).1
  have hpc := (hf.synced k).2
  cases h
  case downgrade_from_M_rq1 v hmem =>
    have hv : v = m := by
      apply hl.release k v
      rw [← hcp]; exact hmem
    refine lvm_step_aux6 hl ?_ ?_ ?_
    · intro v' hmem'
      apply hl.grantM k v'
      rw [← hpc]; exact hmem'
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      have h' := Multiset.mem_of_mem_erase hmem'
      rw [hcp] at h'
      exact hl.release k v' h'
    · intro _; exact hv
  case downgrade_from_M_rq2 hmem =>
    refine lvm_step_aux6 hl ?_ ?_ ?_
    · intro v' hmem'
      apply hl.grantM k v'
      rw [← hpc]; exact hmem'
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      have h' := Multiset.mem_of_mem_erase hmem'
      rw [hcp] at h'
      exact hl.release k v' h'
    · intro h0
      refine hl.parent (lvm_step_aux7 ?_ ?_ h0)
      · exact congrArg (fun s => Multiset.countP (fun e => isGrantM e = true) s) hpc
      · simp only [update_Fin_gss]
        rw [lvm_step_aux2 hmem rfl, hcp]
  case upgrade_to_M_data_avilable_rq1 hall hmem =>
    have hpv : x.parent.value = m := hl.parent (fun i => (hf.rowI i (hall i)).1)
    refine lvm_step_aux6 hl ?_ ?_ ?_
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      rcases Multiset.mem_cons.1 hmem' with h | h
      · rw [PCEvent.rsM.inj h]; exact hpv
      · rw [hpc] at h; exact hl.grantM k v' h
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      have h' := Multiset.mem_of_mem_erase hmem'
      rw [hcp] at h'
      exact hl.release k v' h'
    · intro _; exact hpv
  case upgrade_to_M_data_avilable_rq2 hnoM hmem hI =>
    refine lvm_step_aux6 hl ?_ ?_ ?_
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      rcases Multiset.mem_cons.1 hmem' with h | h
      · exact PCEvent.noConfusion h
      · rw [hpc] at h; exact hl.grantM k v' h
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      have h' := Multiset.mem_of_mem_erase hmem'
      rw [hcp] at h'
      exact hl.release k v' h'
    · intro h0
      refine hl.parent (lvm_step_aux7 ?_ ?_ h0)
      · simp only [update_Fin_gss]
        rw [lvm_step_aux1 _ (rfl : isGrantM (PCEvent.rsS x.parent.value) = false), hpc]
      · simp only [update_Fin_gss]
        rw [lvm_step_aux2 hmem rfl, hcp]
  all_goals
    refine lvm_step_aux6 hl ?_ ?_ ?_
    · intro v' hmem'
      simp only [update_Fin_gss] at hmem'
      rcases Multiset.mem_cons.1 hmem' with h | h
      · exact PCEvent.noConfusion h
      · rw [hpc] at h; exact hl.grantM k v' h
    · intro v' hmem'
      apply hl.release k v'
      rw [← hcp]; exact hmem'
    · intro h0
      refine hl.parent (lvm_step_aux7 ?_ ?_ h0)
      · simp only [update_Fin_gss]
        first
          | rw [lvm_step_aux1 PCEvent.rqIμ rfl, hpc]
          | rw [lvm_step_aux1 PCEvent.rqIσ rfl, hpc]
      · exact congrArg (fun s => Multiset.countP (fun e => isReleaseM e = true) s) hcp

/-- I passi interni copiano valori: la specifica di `m` si conserva. -/
theorem lvm_step {x y : MSIState n} {m : Value} {e : MSIInternalEvent n} (hf : NoBadFacts x)
    (hl : LVM x m) (h : msi_step_internal x e y) : LVM y m := by
  cases h with
  | cache c' k e' hc' =>
    have hfacts := lvm_step_aux4 hc' (hl.cacheM k) (hl.grantM k) (hl.release k)
    exact lvm_step_aux5 hl hfacts.1 hfacts.2.1 hfacts.2.2 (lvm_step_aux3 hc')
  | parent_upd_queue p' e' k hp => exact lvm_step_aux8 hf hl hp

theorem val_step {x y : MSIState n} {e : MSIInternalEvent n} (hx : Good x)
    (h : msi_step_internal x e y) : val y = val x := by
  have hf := noBadFacts_of_good hx
  have hf' := noBadFacts_of_good (good_step hx h)
  exact val_eq_of_lvm hf' (lvm_step hf (lvm_val hf) h)

theorem val_trans {x y : MSIState n} (hx : Good x) (h : trans_refl (msi_rule n) x y) :
    val y = val x := by
  induction h with
  | refl => rfl
  | step hr _ ih =>
    obtain ⟨e, he⟩ := hr
    rw [ih (good_step hx he), val_step hx he]

/-- Senza token `M` il parent vale `val`. -/
theorem val_of_no_mtok {x : MSIState n} (hx : Good x) (h0 : ∀ k, mtok x k = 0) :
    x.parent.value = val x :=
  (lvm_val (noBadFacts_of_good hx)).parent h0

/-! ## Lo stato canonico e le `extqueue` -/

def canon (x : MSIState n) (m : Value) : MSIState n :=
  ⟨fun k => ⟨Bstate.I, m, 0, 0, (x.caches k).extqueue⟩,
   ⟨m, fun _ => Bstate.I, fun _ => 0, fun _ => 0⟩⟩

theorem ext_step {x y : MSIState n} {e : MSIInternalEvent n} (h : msi_step_internal x e y) :
    ∀ k, (y.caches k).extqueue = (x.caches k).extqueue := by
  intro k'
  cases h with
  | cache c' k e' hc' =>
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
      cases hc' <;> rfl
    · simp only [update_Fin_gso2 _ _ _ _ hk]
  | parent_upd_queue p' e' k hp =>
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss]
    · simp only [update_Fin_gso2 _ _ _ _ hk]

theorem ext_trans {x y : MSIState n} (h : trans_refl (msi_rule n) x y) :
    ∀ k, (y.caches k).extqueue = (x.caches k).extqueue := by
  induction h with
  | refl => intro k; rfl
  | step hr _ ih => obtain ⟨e, he⟩ := hr; intro k; rw [ih k, ext_step he k]

theorem canon_ext {x y : MSIState n} {m : Value}
    (h : ∀ k, (x.caches k).extqueue = (y.caches k).extqueue) : canon x m = canon y m := by
  unfold canon
  congr 1
  funext k
  rw [h k]

theorem canon_trans {x y : MSIState n} (hx : Good x) (h : trans_refl (msi_rule n) x y) :
    canon y (val y) = canon x (val x) := by
  rw [val_trans hx h]
  exact canon_ext (ext_trans h)

theorem trans_refl_trans {A : Type} {r : A → A → Prop} {a b c : A} (hab : trans_refl r a b)
    (hbc : trans_refl r b c) : trans_refl r a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact trans_refl.step h (ih hbc)

/-! ## Le misure e il drenaggio -/

/-- Contributo dell'indice `k` alla fase 1: grant in volo, cache non in `I`, rilasci in volo. -/
def m1 (x : MSIState n) (k : Fin n) : Nat :=
  3 * (x.caches k).queue_pc.countP (fun e => isGrant e = true)
    + 2 * (if (x.caches k).state = Bstate.I then 0 else 1)
    + (x.caches k).queue_cp.countP (fun e => isRelease e = true)

def μ1 (x : MSIState n) : Nat := Finset.univ.sum (fun k => m1 x k)
def μ2 (x : MSIState n) : Nat :=
  Finset.univ.sum (fun k => (x.caches k).queue_cp.countP (fun e => isRequest e = true))
def μ3 (x : MSIState n) : Nat :=
  Finset.univ.sum (fun k => (x.caches k).queue_pc.countP (fun e => isInval e = true))
def μ4 (x : MSIState n) (m : Value) : Nat :=
  Finset.univ.sum (fun k => if (x.caches k).value = m then 0 else 1)

/-! ### Fase 1: svuotare cache non in `I`, grant e rilasci -/

/-- Sostituire la cache `k` (non in `I`) con una cache in `I`, stessa `queue_pc` e un rilascio in
più in `queue_cp` fa scendere `μ1` (il parent non conta). -/
theorem phase1_step_release_aux1 {x : MSIState n} {k : Fin n} (hk : (x.caches k).state ≠ Bstate.I)
    {c' : CacheState} (hst : c'.state = Bstate.I) (hpc : c'.queue_pc = (x.caches k).queue_pc)
    (hcp : c'.queue_cp.countP (fun e => isRelease e = true)
      = (x.caches k).queue_cp.countP (fun e => isRelease e = true) + 1)
    (p' : ParentState n) :
    μ1 { caches := update_Fin k c' x.caches, parent := p' } < μ1 x := by
  have hlt : m1 { caches := update_Fin k c' x.caches, parent := p' } k < m1 x k := by
    unfold m1
    simp only [update_Fin_gss]
    rw [hpc, hcp, if_pos hst, if_neg hk]
    omega
  unfold μ1
  apply sum_lt_of_pointwise (k₀ := k) _ hlt
  intro k'
  by_cases hk' : k' = k
  · subst hk'
    exact le_of_lt hlt
  · have heq : m1 { caches := update_Fin k c' x.caches, parent := p' } k' = m1 x k' := by
      unfold m1
      simp only [update_Fin_gso2 _ _ _ _ hk']
    exact le_of_eq heq

/-- Una cache non in `I` rilascia (`rq_data_not_available`/`_1`): `μ1` cala. -/
theorem phase1_step_release {x : MSIState n} {k : Fin n} (hx : Good x)
    (hk : (x.caches k).state ≠ Bstate.I) : ∃ y, msi_rule n x y ∧ μ1 y < μ1 x := by
  cases hst : (x.caches k).state with
  | I => exact absurd hst hk
  | M =>
    refine ⟨_, ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.rq_data_not_available _ hst)⟩, ?_⟩
    refine phase1_step_release_aux1 hk ?_ ?_ ?_ _
    · rfl
    · rfl
    · simp [isRelease]
  | S =>
    refine ⟨_, ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.rq_data_not_available1 _ hst)⟩, ?_⟩
    refine phase1_step_release_aux1 hk ?_ ?_ ?_ _
    · rfl
    · rfl
    · simp [isRelease]

/-- `countP` dopo `erase` di un elemento presente: il conteggio cala di `p a`. -/
theorem phase1_step_proc_aux0 {α : Type} [DecidableEq α] {s : Multiset α} {a : α}
    {p : α → Prop} [DecidablePred p] (h : a ∈ s) :
    (s.erase a).countP p + (if p a then 1 else 0) = s.countP p := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

/-- Un passo del parent all'indice `k` cambia `m1` solo in `k`: se lì cala, cala `μ1`. -/
theorem phase1_step_proc_aux1 {x : MSIState n} {c' : CacheState} {p' : ParentState n} {k : Fin n}
    (hlt : m1 { x with caches := update_Fin k c' x.caches, parent := p' } k < m1 x k) :
    μ1 { x with caches := update_Fin k c' x.caches, parent := p' } < μ1 x := by
  unfold μ1
  refine sum_lt_of_pointwise (fun k' => ?_) k hlt
  by_cases hk : k' = k
  · subst hk
    exact hlt.le
  · apply le_of_eq
    simp only [m1, update_Fin_gso2 _ _ _ _ hk]

/-- Il parent consuma un rilascio (`downgrade_from_M_rq1`/`rq2`): `μ1` cala. -/
theorem phase1_step_proc {x : MSIState n} {k : Fin n} {m : CPEvent} (hx : Good x)
    (hm : m ∈ (x.caches k).queue_cp) (hrel : isRelease m = true) :
    ∃ y, msi_rule n x y ∧ μ1 y < μ1 x := by
  have hs1 := (synced_of_good hx k).1
  have hs2 := (synced_of_good hx k).2
  have hm' : m ∈ x.parent.queue_cip k := by rw [hs1]; exact hm
  have hc := phase1_step_proc_aux0 (p := fun e => isRelease e = true) hm
  rw [if_pos hrel] at hc
  cases m with
  | rsIμ v =>
    refine ⟨_, ⟨_, msi_step_internal.parent_upd_queue x _ _ k
      (parent_msi_step.downgrade_from_M_rq1 x.parent v k hm')⟩, ?_⟩
    apply phase1_step_proc_aux1
    simp only [m1, update_Fin_gss, hs1, hs2]
    omega
  | rsIσ =>
    refine ⟨_, ⟨_, msi_step_internal.parent_upd_queue x _ _ k
      (parent_msi_step.downgrade_from_M_rq2 x.parent k hm')⟩, ?_⟩
    apply phase1_step_proc_aux1
    simp only [m1, update_Fin_gss, hs1, hs2]
    omega
  | rqS => simp [isRelease] at hrel
  | rqM => simp [isRelease] at hrel

/-- Un passo di cache che fa calare `m1` all'indice `k` fa calare `μ1`: gli altri indici non cambiano. -/
theorem phase1_step_take_aux1 {x : MSIState n} {k : Fin n} {c' : CacheState}
    (hlt : m1 { x with caches := update_Fin k c' x.caches,
                       parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                       parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } k < m1 x k) :
    μ1 { x with caches := update_Fin k c' x.caches,
                parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } < μ1 x := by
  unfold μ1
  refine sum_lt_of_pointwise (fun k' => ?_) k hlt
  by_cases hk : k' = k
  · subst hk
    exact le_of_lt hlt
  · unfold m1
    simp only [update_Fin_gso2 _ _ _ _ hk]
    exact le_refl _

/-- Una cache in `I` prende un grant (`upgrade_from_I_rs`/`_rsS`): `μ1` cala. -/
theorem phase1_step_take {x : MSIState n} {k : Fin n} {m : PCEvent} (hx : Good x)
    (hI : (x.caches k).state = Bstate.I) (hm : m ∈ (x.caches k).queue_pc) (hg : isGrant m = true) :
    ∃ y, msi_rule n x y ∧ μ1 y < μ1 x := by
  have hc := phase1_step_proc_aux0 (p := fun e => isGrant e = true) hm
  rw [if_pos hg] at hc
  cases m with
  | rqIμ => simp [isGrant] at hg
  | rqIσ => simp [isGrant] at hg
  | rsM v =>
    have hstep := cache_msi_step_internal.upgrade_from_I_rs (x.caches k) v hm hI
    refine ⟨_, ⟨_, msi_step_internal.cache x _ k _ hstep⟩, phase1_step_take_aux1 ?_⟩
    unfold m1
    simp only [update_Fin_gss]
    rw [if_pos hI, if_neg (fun h => Bstate.noConfusion h)]
    omega
  | rsS v =>
    have hstep := cache_msi_step_internal.upgrade_from_I_rsS (x.caches k) v hm hI
    refine ⟨_, ⟨_, msi_step_internal.cache x _ k _ hstep⟩, phase1_step_take_aux1 ?_⟩
    unfold m1
    simp only [update_Fin_gss]
    rw [if_pos hI, if_neg (fun h => Bstate.noConfusion h)]
    omega

theorem phase1_step {x : MSIState n} (hx : Good x) (hpos : 0 < μ1 x) :
    ∃ y, msi_rule n x y ∧ μ1 y < μ1 x := by
  by_cases hall : ∀ k, (x.caches k).state = Bstate.I
  · unfold μ1 at hpos
    obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
    have hk' : 0 < m1 x k := hk
    unfold m1 at hk'
    rw [if_pos (hall k)] at hk'
    have hcases : 0 < (x.caches k).queue_pc.countP (fun e => isGrant e = true)
        ∨ 0 < (x.caches k).queue_cp.countP (fun e => isRelease e = true) := by omega
    rcases hcases with hg | hr
    · obtain ⟨m, hm, hmg⟩ := Multiset.countP_pos.mp hg
      exact phase1_step_take hx (hall k) hm hmg
    · obtain ⟨m, hm, hmr⟩ := Multiset.countP_pos.mp hr
      exact phase1_step_proc hx hm hmr
  · obtain ⟨k, hk⟩ := not_forall.mp hall
    exact phase1_step_release hx hk

theorem phase1 {x : MSIState n} (hx : Good x) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 := by
  suffices H : ∀ m, ∀ x : MSIState n, Good x → μ1 x ≤ m →
      ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 from H _ x hx le_rfl
  intro m
  induction m with
  | zero =>
    intro x hx hm
    exact ⟨x, trans_refl.refl, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hx hm
    by_cases h0 : μ1 x = 0
    · exact ⟨x, trans_refl.refl, h0⟩
    · obtain ⟨y, hxy, hlt⟩ := phase1_step hx (Nat.pos_of_ne_zero h0)
      obtain ⟨e, he⟩ := hxy
      obtain ⟨z, hyz, hz⟩ := ih y (good_step hx he) (by omega)
      exact ⟨z, trans_refl.step ⟨e, he⟩ hyz, hz⟩

/-! ### Che cosa dice `μ1 x = 0` -/

theorem quiet_caches {x : MSIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).state = Bstate.I := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  by_cases hs : (x.caches k).state = Bstate.I
  · exact hs
  · rw [if_neg hs] at hk
    omega

theorem quiet_grants {x : MSIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).queue_pc.countP (fun e => isGrant e = true) = 0 := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  omega

theorem quiet_releases {x : MSIState n} (h0 : μ1 x = 0) (k : Fin n) :
    (x.caches k).queue_cp.countP (fun e => isRelease e = true) = 0 := by
  have h0' : Finset.univ.sum (fun k => m1 x k) = 0 := h0
  have hk : m1 x k = 0 := sum_eq_zero_iff_pointwise.mp h0' k
  unfold m1 at hk
  omega

theorem quiet_of {x : MSIState n} (hc : ∀ k, (x.caches k).state = Bstate.I)
    (hg : ∀ k, (x.caches k).queue_pc.countP (fun e => isGrant e = true) = 0)
    (hr : ∀ k, (x.caches k).queue_cp.countP (fun e => isRelease e = true) = 0) : μ1 x = 0 := by
  show Finset.univ.sum (fun k => m1 x k) = 0
  apply sum_eq_zero_iff_pointwise.mpr
  intro k
  show m1 x k = 0
  unfold m1
  simp [hg k, hr k, hc k]

/-- Niente grant ⇒ niente grant `M`. -/
theorem quiet_mtok_aux1 {s : Multiset PCEvent}
    (h : s.countP (fun e => isGrant e = true) = 0) :
    s.countP (fun e => isGrantM e = true) = 0 := by
  rw [Multiset.countP_eq_zero] at h ⊢
  intro a ha hga
  apply h a ha
  cases a <;> simp [isGrantM, isGrant] at hga ⊢

/-- Niente rilasci ⇒ niente rilasci `M`. -/
theorem quiet_mtok_aux2 {s : Multiset CPEvent}
    (h : s.countP (fun e => isRelease e = true) = 0) :
    s.countP (fun e => isReleaseM e = true) = 0 := by
  rw [Multiset.countP_eq_zero] at h ⊢
  intro a ha hga
  apply h a ha
  cases a <;> simp [isReleaseM, isRelease] at hga ⊢

theorem quiet_mtok {x : MSIState n} (h0 : μ1 x = 0) (k : Fin n) : mtok x k = 0 := by
  have hc := quiet_caches h0 k
  have hg := quiet_mtok_aux1 (quiet_grants h0 k)
  have hr := quiet_mtok_aux2 (quiet_releases h0 k)
  unfold mtok mtokC
  rw [hc, hg, hr]
  simp

/-- Niente grant ⇒ niente grant `S`. -/
theorem quiet_stok_aux1 {s : Multiset PCEvent}
    (h : s.countP (fun e => isGrant e = true) = 0) :
    s.countP (fun e => isGrantS e = true) = 0 := by
  rw [Multiset.countP_eq_zero] at h ⊢
  intro a ha hga
  apply h a ha
  cases a <;> simp [isGrantS, isGrant] at hga ⊢

/-- Niente rilasci ⇒ niente rilasci `S`. -/
theorem quiet_stok_aux2 {s : Multiset CPEvent}
    (h : s.countP (fun e => isRelease e = true) = 0) :
    s.countP (fun e => isReleaseS e = true) = 0 := by
  rw [Multiset.countP_eq_zero] at h ⊢
  intro a ha hga
  apply h a ha
  cases a <;> simp [isReleaseS, isRelease] at hga ⊢

theorem quiet_stok {x : MSIState n} (h0 : μ1 x = 0) (k : Fin n) : stok x k = 0 := by
  have hc := quiet_caches h0 k
  have hg := quiet_stok_aux1 (quiet_grants h0 k)
  have hr := quiet_stok_aux2 (quiet_releases h0 k)
  unfold stok stokC
  rw [hc, hg, hr]
  simp

/-- Senza token, le righe sono a `I` (dalle viste: una riga `M`/`S` ha un token). -/
theorem quiet_rows {x : MSIState n} (hx : Good x) (h0 : μ1 x = 0) (k : Fin n) :
    x.parent.shared_state k = Bstate.I := by
  have hf := noBadFacts_of_good hx
  have hm := quiet_mtok h0 k
  have hs := quiet_stok h0 k
  cases hrow : x.parent.shared_state k with
  | I => rfl
  | M =>
    have h1 := (hf.rowM k hrow).1
    rw [hm] at h1
    omega
  | S =>
    have h1 := (hf.rowS k hrow).1
    rw [hs] at h1
    omega

/-! ### Fase 2: consumare le richieste pendenti -/

/-- `countP` dopo `erase` di un elemento presente: il conteggio cala di `p a`. -/
theorem phase2_step_M_aux0 {α : Type} [DecidableEq α] {s : Multiset α} {a : α}
    {p : α → Prop} [DecidablePred p] (h : a ∈ s) :
    (s.erase a).countP p + (if p a then 1 else 0) = s.countP p := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

/-- Lo stato finale della fase 2 per l'indice `k`: cache `k` in `I`, stessa `queue_pc`, una
richiesta `r` tolta da `queue_cp`, le altre cache invariate. Allora `μ1 = 0`, `μ2` cala, `μ3` è
invariata. -/
theorem phase2_step_M_aux1 {x y : MSIState n} {k : Fin n} {r : CPEvent} (h0 : μ1 x = 0)
    (hm : r ∈ (x.caches k).queue_cp) (hreq : isRequest r = true) (hrel : isRelease r = false)
    (hstate : (y.caches k).state = Bstate.I)
    (hpc : (y.caches k).queue_pc = (x.caches k).queue_pc)
    (hcp : (y.caches k).queue_cp = (x.caches k).queue_cp.erase r)
    (hoth : ∀ k', k' ≠ k → y.caches k' = x.caches k') :
    μ1 y = 0 ∧ μ2 y < μ2 x ∧ μ3 y = μ3 x := by
  have hall := quiet_caches h0
  have hg := quiet_grants h0
  have hr := quiet_releases h0
  have hreqc := phase2_step_M_aux0 (p := fun e => isRequest e = true) hm
  rw [if_pos hreq] at hreqc
  have hrelc := phase2_step_M_aux0 (p := fun e => isRelease e = true) hm
  rw [if_neg (show ¬ (isRelease r = true) by rw [hrel]; exact Bool.false_ne_true)] at hrelc
  refine ⟨?_, ?_, ?_⟩
  · -- `μ1 y = 0`
    have hc : ∀ k', (y.caches k').state = Bstate.I := by
      intro k'
      by_cases hk : k' = k
      · rw [hk]; exact hstate
      · rw [hoth k' hk]; exact hall k'
    have hg' : ∀ k', (y.caches k').queue_pc.countP (fun e => isGrant e = true) = 0 := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, hpc]; exact hg k
      · rw [hoth k' hk]; exact hg k'
    have hr' : ∀ k', (y.caches k').queue_cp.countP (fun e => isRelease e = true) = 0 := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, hcp]
        have := hr k
        omega
      · rw [hoth k' hk]; exact hr k'
    exact quiet_of hc hg' hr'
  · -- `μ2 y < μ2 x`
    have hle : ∀ k', (y.caches k').queue_cp.countP (fun e => isRequest e = true)
        ≤ (x.caches k').queue_cp.countP (fun e => isRequest e = true) := by
      intro k'
      by_cases hk : k' = k
      · rw [hk, hcp]; omega
      · rw [hoth k' hk]
    have hlt : (y.caches k).queue_cp.countP (fun e => isRequest e = true)
        < (x.caches k).queue_cp.countP (fun e => isRequest e = true) := by
      rw [hcp]; omega
    unfold μ2
    exact sum_lt_of_pointwise hle k hlt
  · -- `μ3 y = μ3 x`
    unfold μ3
    apply Finset.sum_congr rfl
    intro k' _
    by_cases hk : k' = k
    · rw [hk, hpc]
    · rw [hoth k' hk]

/-- Una `rqM` pendente con tutto a `I`: grant, presa, rilascio, consumo (4 passi). -/
theorem phase2_step_M {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0)
    (hm : CPEvent.rqM ∈ (x.caches k).queue_cp) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x ∧ μ3 y = μ3 x := by
  have hs : synced x := synced_of_good hx
  have hall := quiet_caches h0
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hx h0
  have hm1 : CPEvent.rqM ∈ x.parent.queue_cip k := by rw [(hs k).1]; exact hm
  -- Passo 1: il parent concede `M` a `k`.
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, msi_rule n x x1
        ∧ synced x1
        ∧ (x1.caches k).state = Bstate.I
        ∧ (x1.caches k).queue_pc = PCEvent.rsM x.parent.value ::ₘ (x.caches k).queue_pc
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqM
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    have hstep := msi_step_internal.parent_upd_queue x _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq1 x.parent k hm1 hrows)
    refine ⟨_, ⟨_, hstep⟩, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact hall k
    · simp only [update_Fin_gss]; rw [(hs k).2]
    · simp only [update_Fin_gss]; rw [(hs k).1]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: la cache `k` prende il grant.
  obtain ⟨x2, step2, h2s, h2state, h2pc, h2cp, h2val, h2oth⟩ :
      ∃ x2, msi_rule n x1 x2
        ∧ synced x2
        ∧ (x2.caches k).state = Bstate.M
        ∧ (x2.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqM
        ∧ (x2.caches k).value = x.parent.value
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    have hg3 : PCEvent.rsM x.parent.value ∈ (x1.caches k).queue_pc := by
      rw [h1pc]; exact Multiset.mem_cons_self _ _
    have hstep := msi_step_internal.cache x1 _ k _
      (cache_msi_step_internal.upgrade_from_I_rs (x1.caches k) x.parent.value hg3 h1state)
    refine ⟨_, ⟨_, hstep⟩, synced_step h1s hstep, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; rw [h1pc]; exact Multiset.erase_cons_head _ _
    · simp only [update_Fin_gss]; exact h1cp
    · simp only [update_Fin_gss]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  -- Passo 3: la cache `k` rilascia spontaneamente.
  obtain ⟨x3, step3, h3s, h3state, h3pc, h3cp, h3oth⟩ :
      ∃ x3, msi_rule n x2 x3
        ∧ synced x3
        ∧ (x3.caches k).state = Bstate.I
        ∧ (x3.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x3.caches k).queue_cp
            = CPEvent.rsIμ x.parent.value ::ₘ (x.caches k).queue_cp.erase CPEvent.rqM
        ∧ (∀ k', k' ≠ k → x3.caches k' = x.caches k') := by
    have hstep := msi_step_internal.cache x2 _ k _
      (cache_msi_step_internal.rq_data_not_available (x2.caches k) h2state)
    refine ⟨_, ⟨_, hstep⟩, synced_step h2s hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; exact h2pc
    · simp only [update_Fin_gss]; rw [h2cp, h2val]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h2oth k' hk
  -- Passo 4: il parent prende il rilascio.
  obtain ⟨x4, step4, h4state, h4pc, h4cp, h4oth⟩ :
      ∃ x4, msi_rule n x3 x4
        ∧ (x4.caches k).state = Bstate.I
        ∧ (x4.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x4.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqM
        ∧ (∀ k', k' ≠ k → x4.caches k' = x.caches k') := by
    have hg6 : CPEvent.rsIμ x.parent.value ∈ x3.parent.queue_cip k := by
      rw [(h3s k).1, h3cp]; exact Multiset.mem_cons_self _ _
    have hstep := msi_step_internal.parent_upd_queue x3 _ _ k
      (parent_msi_step.downgrade_from_M_rq1 x3.parent x.parent.value k hg6)
    refine ⟨_, ⟨_, hstep⟩, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h3state
    · simp only [update_Fin_gss]; rw [(h3s k).2, h3pc]
    · simp only [update_Fin_gss]; rw [(h3s k).1, h3cp]; exact Multiset.erase_cons_head _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h3oth k' hk
  -- Conclusione.
  exact ⟨x4, trans_refl.step step1 (trans_refl.step step2 (trans_refl.step step3
    (trans_refl.step step4 trans_refl.refl))),
    phase2_step_M_aux1 h0 hm rfl rfl h4state h4pc h4cp h4oth⟩

/-- Una `rqS` pendente con tutto a `I`: grant, presa, rilascio, consumo (4 passi). -/
theorem phase2_step_S {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0)
    (hm : CPEvent.rqS ∈ (x.caches k).queue_cp) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x ∧ μ3 y = μ3 x := by
  have hs : synced x := synced_of_good hx
  have hall := quiet_caches h0
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hx h0
  have hnoM : ∀ i, ¬ x.parent.shared_state i = Bstate.M := fun i h => by
    rw [hrows i] at h; exact Bstate.noConfusion h
  have hm1 : CPEvent.rqS ∈ x.parent.queue_cip k := by rw [(hs k).1]; exact hm
  -- Passo 1: il parent concede `S` a `k`.
  obtain ⟨x1, step1, h1s, h1state, h1pc, h1cp, h1oth⟩ :
      ∃ x1, msi_rule n x x1
        ∧ synced x1
        ∧ (x1.caches k).state = Bstate.I
        ∧ (x1.caches k).queue_pc = PCEvent.rsS x.parent.value ::ₘ (x.caches k).queue_pc
        ∧ (x1.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqS
        ∧ (∀ k', k' ≠ k → x1.caches k' = x.caches k') := by
    have hstep := msi_step_internal.parent_upd_queue x _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 x.parent k hm1 (hrows k) hnoM)
    refine ⟨_, ⟨_, hstep⟩, synced_step hs hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact hall k
    · simp only [update_Fin_gss]; rw [(hs k).2]
    · simp only [update_Fin_gss]; rw [(hs k).1]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]
  -- Passo 2: la cache `k` prende il grant.
  obtain ⟨x2, step2, h2s, h2state, h2pc, h2cp, h2oth⟩ :
      ∃ x2, msi_rule n x1 x2
        ∧ synced x2
        ∧ (x2.caches k).state = Bstate.S
        ∧ (x2.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x2.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqS
        ∧ (∀ k', k' ≠ k → x2.caches k' = x.caches k') := by
    have hg3 : PCEvent.rsS x.parent.value ∈ (x1.caches k).queue_pc := by
      rw [h1pc]; exact Multiset.mem_cons_self _ _
    have hstep := msi_step_internal.cache x1 _ k _
      (cache_msi_step_internal.upgrade_from_I_rsS (x1.caches k) x.parent.value hg3 h1state)
    refine ⟨_, ⟨_, hstep⟩, synced_step h1s hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; rw [h1pc]; exact Multiset.erase_cons_head _ _
    · simp only [update_Fin_gss]; exact h1cp
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h1oth k' hk
  -- Passo 3: la cache `k` rilascia spontaneamente.
  obtain ⟨x3, step3, h3s, h3state, h3pc, h3cp, h3oth⟩ :
      ∃ x3, msi_rule n x2 x3
        ∧ synced x3
        ∧ (x3.caches k).state = Bstate.I
        ∧ (x3.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x3.caches k).queue_cp = CPEvent.rsIσ ::ₘ (x.caches k).queue_cp.erase CPEvent.rqS
        ∧ (∀ k', k' ≠ k → x3.caches k' = x.caches k') := by
    have hstep := msi_step_internal.cache x2 _ k _
      (cache_msi_step_internal.rq_data_not_available1 (x2.caches k) h2state)
    refine ⟨_, ⟨_, hstep⟩, synced_step h2s hstep, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]
    · simp only [update_Fin_gss]; exact h2pc
    · simp only [update_Fin_gss]; rw [h2cp]
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h2oth k' hk
  -- Passo 4: il parent prende il rilascio.
  obtain ⟨x4, step4, h4state, h4pc, h4cp, h4oth⟩ :
      ∃ x4, msi_rule n x3 x4
        ∧ (x4.caches k).state = Bstate.I
        ∧ (x4.caches k).queue_pc = (x.caches k).queue_pc
        ∧ (x4.caches k).queue_cp = (x.caches k).queue_cp.erase CPEvent.rqS
        ∧ (∀ k', k' ≠ k → x4.caches k' = x.caches k') := by
    have hg6 : CPEvent.rsIσ ∈ x3.parent.queue_cip k := by
      rw [(h3s k).1, h3cp]; exact Multiset.mem_cons_self _ _
    have hstep := msi_step_internal.parent_upd_queue x3 _ _ k
      (parent_msi_step.downgrade_from_M_rq2 x3.parent k hg6)
    refine ⟨_, ⟨_, hstep⟩, ?_, ?_, ?_, ?_⟩
    · simp only [update_Fin_gss]; exact h3state
    · simp only [update_Fin_gss]; rw [(h3s k).2, h3pc]
    · simp only [update_Fin_gss]; rw [(h3s k).1, h3cp]; exact Multiset.erase_cons_head _ _
    · intro k' hk; simp only [update_Fin_gso2 _ _ _ _ hk]; exact h3oth k' hk
  -- Conclusione.
  exact ⟨x4, trans_refl.step step1 (trans_refl.step step2 (trans_refl.step step3
    (trans_refl.step step4 trans_refl.refl))),
    phase2_step_M_aux1 h0 hm rfl rfl h4state h4pc h4cp h4oth⟩

theorem phase2_step {x : MSIState n} (hx : Good x) (h0 : μ1 x = 0) (hpos : 0 < μ2 x) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y < μ2 x ∧ μ3 y = μ3 x := by
  unfold μ2 at hpos
  obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
  obtain ⟨m, hm, hmr⟩ := Multiset.countP_pos.mp hk
  cases m with
  | rsIμ v => simp [isRequest] at hmr
  | rsIσ => simp [isRequest] at hmr
  | rqS => exact phase2_step_S hx h0 hm
  | rqM => exact phase2_step_M hx h0 hm

theorem phase2 {x : MSIState n} (hx : Good x) (h0 : μ1 x = 0) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 := by
  suffices H : ∀ m, ∀ x : MSIState n, Good x → μ1 x = 0 → μ2 x ≤ m →
      ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 from
    H _ x hx h0 le_rfl
  intro m
  induction m with
  | zero =>
    intro x hx h0 hm
    exact ⟨x, trans_refl.refl, h0, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hx h0 hm
    by_cases h2 : μ2 x = 0
    · exact ⟨x, trans_refl.refl, h0, h2⟩
    · obtain ⟨y, hxy, h0y, hlt, _⟩ := phase2_step hx h0 (Nat.pos_of_ne_zero h2)
      obtain ⟨z, hyz, h0z, h2z⟩ := ih y (good_trans hx hxy) h0y (by omega)
      exact ⟨z, trans_refl_trans hxy hyz, h0z, h2z⟩

/-! ### Fase 3: consumare gli invalidate stantii -/

/-- `countP` dopo `erase` di un elemento presente: il conteggio cala di `p a`. -/
theorem phase3_step_M_aux0 {α : Type} [DecidableEq α] {s : Multiset α} {a : α}
    {p : α → Prop} [DecidablePred p] (h : a ∈ s) :
    (s.erase a).countP p + (if p a then 1 else 0) = s.countP p := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

/-- Le misure dopo i cinque passi: la cache `k` ha perso un invalidate `m` dalla sua `queue_pc`
(e ha cambiato valore), le altre cache sono invariate: `μ1` e `μ2` restano a zero, `μ3` cala. -/
theorem phase3_step_M_aux1 {x y : MSIState n} {k : Fin n} {m : PCEvent} {v : Value}
    (h0 : μ1 x = 0) (h2 : μ2 x = 0) (hm : m ∈ (x.caches k).queue_pc)
    (hi : isInval m = true) (hg : ¬ isGrant m = true)
    (hyk : y.caches k = { x.caches k with value := v, queue_pc := (x.caches k).queue_pc.erase m })
    (hyo : ∀ k', k' ≠ k → y.caches k' = x.caches k') :
    μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  have hcI := phase3_step_M_aux0 (p := fun e => isInval e = true) hm
  rw [if_pos hi] at hcI
  have hcG := phase3_step_M_aux0 (p := fun e => isGrant e = true) hm
  rw [if_neg hg] at hcG
  refine ⟨?_, ?_, ?_⟩
  · apply quiet_of
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]; exact quiet_caches h0 k
      · rw [hyo k' hk]; exact quiet_caches h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]
        show ((x.caches k).queue_pc.erase m).countP (fun e => isGrant e = true) = 0
        have := quiet_grants h0 k
        omega
      · rw [hyo k' hk]; exact quiet_grants h0 k'
    · intro k'
      by_cases hk : k' = k
      · rw [hk, hyk]; exact quiet_releases h0 k
      · rw [hyo k' hk]; exact quiet_releases h0 k'
  · have h2' := sum_eq_zero_iff_pointwise.1 h2
    unfold μ2
    refine sum_eq_zero_iff_pointwise.2 fun k' => ?_
    show (y.caches k').queue_cp.countP (fun e => isRequest e = true) = 0
    by_cases hk : k' = k
    · rw [hk, hyk]; exact h2' k
    · rw [hyo k' hk]; exact h2' k'
  · unfold μ3
    refine sum_lt_of_pointwise (fun k' => ?_) k ?_
    · show (y.caches k').queue_pc.countP (fun e => isInval e = true)
        ≤ (x.caches k').queue_pc.countP (fun e => isInval e = true)
      by_cases hk : k' = k
      · rw [hk, hyk]
        show ((x.caches k).queue_pc.erase m).countP (fun e => isInval e = true) ≤ _
        omega
      · rw [hyo k' hk]
    · show (y.caches k).queue_pc.countP (fun e => isInval e = true)
        < (x.caches k).queue_pc.countP (fun e => isInval e = true)
      rw [hyk]
      show ((x.caches k).queue_pc.erase m).countP (fun e => isInval e = true) < _
      omega

/-- I cinque passi di `phase3_step_M`: `rqM`, grant di `M`, presa del grant, `downgrade_from_M_rs`
(consuma l'invalidate e rilascia), presa del rilascio. Lo stato di arrivo ha la cache `k` con il
valore del parent e senza il `rqIμ`, le altre cache invariate. -/
theorem phase3_step_M_aux2 {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0)
    (hm : PCEvent.rqIμ ∈ (x.caches k).queue_pc) :
    ∃ y, trans_refl (msi_rule n) x y ∧
      y.caches k = { x.caches k with
          value := x.parent.value, queue_pc := (x.caches k).queue_pc.erase PCEvent.rqIμ } ∧
      ∀ k', k' ≠ k → y.caches k' = x.caches k' := by
  have hc0 : (x.caches k).state = Bstate.I := quiet_caches h0 k
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hx h0
  refine ⟨?_, ?chain, ?eqk, ?eqo⟩
  case chain =>
    -- 1. la cache `k` chiede `M`
    refine trans_refl.step ⟨_, msi_step_internal.cache x _ k _
      (cache_msi_step_internal.upgrade_from_I_rq _ hc0)⟩ ?_
    -- 2. il parent concede `M` (tutte le righe a `I`)
    refine trans_refl.step ⟨_, msi_step_internal.parent_upd_queue _ _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ k ?g21 ?g22)⟩ ?_
    case g21 =>
      simp only [update_Fin_gss]
      exact Multiset.mem_cons_self _ _
    case g22 => intro i; exact hrows i
    -- 3. la cache `k` prende il grant di `M`
    refine trans_refl.step ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.upgrade_from_I_rs _ x.parent.value ?g31 ?g32)⟩ ?_
    case g31 =>
      simp only [update_Fin_gss]
      exact Multiset.mem_cons_self _ _
    case g32 => simp only [update_Fin_gss, hc0]
    -- 4. la cache `k` consuma il `rqIμ` stantio e rilascia
    refine trans_refl.step ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.downgrade_from_M_rs _ ?g41 ?g42)⟩ ?_
    case g41 => simpa only [update_Fin_gss, Multiset.erase_cons_head] using hm
    case g42 => simp only [update_Fin_gss]
    -- 5. il parent prende il rilascio `rsIμ`
    refine trans_refl.step ⟨_, msi_step_internal.parent_upd_queue _ _ _ k
      (parent_msi_step.downgrade_from_M_rq1 _ x.parent.value k ?g51)⟩ ?_
    case g51 =>
      simp only [update_Fin_gss, Multiset.erase_cons_head]
      exact Multiset.mem_cons_self _ _
    exact trans_refl.refl
  case eqk => simp only [update_Fin_gss, Multiset.erase_cons_head, hc0]
  case eqo =>
    intro k' hk
    simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Un `rqIμ` stantio: la cache chiede `M`, lo prende, consuma l'invalidate rilasciando, il parent
consuma (5 passi): `μ3` cala, `μ1` e `μ2` restano a zero. -/
theorem phase3_step_M {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0) (h2 : μ2 x = 0)
    (hm : PCEvent.rqIμ ∈ (x.caches k).queue_pc) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  obtain ⟨y, hxy, hyk, hyo⟩ := phase3_step_M_aux2 hx h0 hm
  obtain ⟨h1, h2', h3⟩ := phase3_step_M_aux1 h0 h2 hm rfl (by simp [isGrant]) hyk hyo
  exact ⟨y, hxy, h1, h2', h3⟩

/-- I cinque passi di `phase3_step_S`: `rqS`, grant di `S`, presa del grant,
`downgrade_from_M_rs1` (consuma l'invalidate e rilascia), presa del rilascio. -/
theorem phase3_step_S_aux1 {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0)
    (hm : PCEvent.rqIσ ∈ (x.caches k).queue_pc) :
    ∃ y, trans_refl (msi_rule n) x y ∧
      y.caches k = { x.caches k with
          value := x.parent.value, queue_pc := (x.caches k).queue_pc.erase PCEvent.rqIσ } ∧
      ∀ k', k' ≠ k → y.caches k' = x.caches k' := by
  have hc0 : (x.caches k).state = Bstate.I := quiet_caches h0 k
  have hrows : ∀ i, x.parent.shared_state i = Bstate.I := quiet_rows hx h0
  refine ⟨?_, ?chain, ?eqk, ?eqo⟩
  case chain =>
    -- 1. la cache `k` chiede `S`
    refine trans_refl.step ⟨_, msi_step_internal.cache x _ k _
      (cache_msi_step_internal.upgrade_from_I_rq1 _ hc0)⟩ ?_
    -- 2. il parent concede `S` (riga di `k` a `I`, nessuna riga a `M`)
    refine trans_refl.step ⟨_, msi_step_internal.parent_upd_queue _ _ _ k
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ k ?g21 ?g22 ?g23)⟩ ?_
    case g21 =>
      simp only [update_Fin_gss]
      exact Multiset.mem_cons_self _ _
    case g22 => exact hrows k
    case g23 =>
      intro i h
      have h' : x.parent.shared_state i = Bstate.M := h
      rw [hrows i] at h'
      cases h'
    -- 3. la cache `k` prende il grant di `S`
    refine trans_refl.step ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.upgrade_from_I_rsS _ x.parent.value ?g31 ?g32)⟩ ?_
    case g31 =>
      simp only [update_Fin_gss]
      exact Multiset.mem_cons_self _ _
    case g32 => simp only [update_Fin_gss, hc0]
    -- 4. la cache `k` consuma il `rqIσ` stantio e rilascia
    refine trans_refl.step ⟨_, msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.downgrade_from_M_rs1 _ ?g41 ?g42)⟩ ?_
    case g41 => simpa only [update_Fin_gss, Multiset.erase_cons_head] using hm
    case g42 => simp only [update_Fin_gss]
    -- 5. il parent prende il rilascio `rsIσ`
    refine trans_refl.step ⟨_, msi_step_internal.parent_upd_queue _ _ _ k
      (parent_msi_step.downgrade_from_M_rq2 _ k ?g51)⟩ ?_
    case g51 =>
      simp only [update_Fin_gss, Multiset.erase_cons_head]
      exact Multiset.mem_cons_self _ _
    exact trans_refl.refl
  case eqk => simp only [update_Fin_gss, Multiset.erase_cons_head, hc0]
  case eqo =>
    intro k' hk
    simp only [update_Fin_gso2 _ _ _ _ hk]

/-- Un `rqIσ` stantio: la cache chiede `S`, lo prende, consuma l'invalidate rilasciando, il parent
consuma (5 passi). -/
theorem phase3_step_S {x : MSIState n} {k : Fin n} (hx : Good x) (h0 : μ1 x = 0) (h2 : μ2 x = 0)
    (hm : PCEvent.rqIσ ∈ (x.caches k).queue_pc) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  obtain ⟨y, hxy, hyk, hyo⟩ := phase3_step_S_aux1 hx h0 hm
  obtain ⟨h1, h2', h3⟩ := phase3_step_M_aux1 h0 h2 hm rfl (by simp [isGrant]) hyk hyo
  exact ⟨y, hxy, h1, h2', h3⟩

theorem phase3_step {x : MSIState n} (hx : Good x) (h0 : μ1 x = 0) (h2 : μ2 x = 0)
    (hpos : 0 < μ3 x) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y < μ3 x := by
  unfold μ3 at hpos
  obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
  have hk' : 0 < (x.caches k).queue_pc.countP (fun e => isInval e = true) := hk
  obtain ⟨m, hm, hmi⟩ := Multiset.countP_pos.mp hk'
  cases m with
  | rsM v => simp [isInval] at hmi
  | rsS v => simp [isInval] at hmi
  | rqIμ => exact phase3_step_M hx h0 h2 hm
  | rqIσ => exact phase3_step_S hx h0 h2 hm

theorem phase3 {x : MSIState n} (hx : Good x) (h0 : μ1 x = 0) (h2 : μ2 x = 0) :
    ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y = 0 := by
  suffices H : ∀ m, ∀ x : MSIState n, Good x → μ1 x = 0 → μ2 x = 0 → μ3 x ≤ m →
      ∃ y, trans_refl (msi_rule n) x y ∧ μ1 y = 0 ∧ μ2 y = 0 ∧ μ3 y = 0 from
    H _ x hx h0 h2 le_rfl
  intro m
  induction m with
  | zero =>
    intro x hx h0 h2 hm
    exact ⟨x, trans_refl.refl, h0, h2, Nat.le_zero.mp hm⟩
  | succ m ih =>
    intro x hx h0 h2 hm
    by_cases h3 : μ3 x = 0
    · exact ⟨x, trans_refl.refl, h0, h2, h3⟩
    · obtain ⟨y, hxy, h0y, h2y, hlt⟩ := phase3_step hx h0 h2 (Nat.pos_of_ne_zero h3)
      obtain ⟨z, hyz, h0z, h2z, h3z⟩ := ih y (good_trans hx hxy) h0y h2y (by omega)
      exact ⟨z, trans_refl_trans hxy hyz, h0z, h2z, h3z⟩

/-! ### A misure nulle lo stato è quieto -/

/-- Stato quieto: tutte le cache in `I`, code vuote, righe a `I`. -/
structure Quiet (x : MSIState n) : Prop where
  caches : ∀ k, (x.caches k).state = Bstate.I
  cp : ∀ k, (x.caches k).queue_cp = 0
  pc : ∀ k, (x.caches k).queue_pc = 0
  rows : ∀ k, x.parent.shared_state k = Bstate.I
  cip : ∀ k, x.parent.queue_cip k = 0
  pci : ∀ k, x.parent.queue_pci k = 0

theorem quiet_of_measures {x : MSIState n} (hx : Good x) (h1 : μ1 x = 0) (h2 : μ2 x = 0)
    (h3 : μ3 x = 0) : Quiet x := by
  have hcp : ∀ k, (x.caches k).queue_cp = 0 := by
    intro k
    have hr := quiet_releases h1 k
    have h2' : Finset.univ.sum
        (fun k => (x.caches k).queue_cp.countP (fun e => isRequest e = true)) = 0 := h2
    have hq : (x.caches k).queue_cp.countP (fun e => isRequest e = true) = 0 :=
      sum_eq_zero_iff_pointwise.mp h2' k
    rw [Multiset.countP_eq_zero] at hr hq
    apply Multiset.eq_zero_of_forall_notMem
    intro m hm
    cases m
    · exact hr _ hm rfl
    · exact hr _ hm rfl
    · exact hq _ hm rfl
    · exact hq _ hm rfl
  have hpc : ∀ k, (x.caches k).queue_pc = 0 := by
    intro k
    have hg := quiet_grants h1 k
    have h3' : Finset.univ.sum
        (fun k => (x.caches k).queue_pc.countP (fun e => isInval e = true)) = 0 := h3
    have hq : (x.caches k).queue_pc.countP (fun e => isInval e = true) = 0 :=
      sum_eq_zero_iff_pointwise.mp h3' k
    rw [Multiset.countP_eq_zero] at hg hq
    apply Multiset.eq_zero_of_forall_notMem
    intro m hm
    cases m
    · exact hq _ hm rfl
    · exact hq _ hm rfl
    · exact hg _ hm rfl
    · exact hg _ hm rfl
  have hs := synced_of_good hx
  refine ⟨quiet_caches h1, hcp, hpc, quiet_rows hx h1, ?_, ?_⟩
  · intro k
    rw [(hs k).1, hcp k]
  · intro k
    rw [(hs k).2, hpc k]

theorem reach_quiet {x : MSIState n} (hx : Good x) :
    ∃ y, trans_refl (msi_rule n) x y ∧ Quiet y := by
  obtain ⟨y1, h1, hq1⟩ := phase1 hx
  obtain ⟨y2, h2, hq1', hq2⟩ := phase2 (good_trans hx h1) hq1
  obtain ⟨y3, h3, hq1'', hq2', hq3⟩ := phase3 (good_trans (good_trans hx h1) h2) hq1' hq2
  have hy3 : Good y3 := good_trans (good_trans (good_trans hx h1) h2) h3
  exact ⟨y3, trans_refl_trans h1 (trans_refl_trans h2 h3), quiet_of_measures hy3 hq1'' hq2' hq3⟩

theorem val_of_quiet {x : MSIState n} (hx : Good x) (hq : Quiet x) : val x = x.parent.value := by
  have h0 : ∀ k, mtok x k = 0 := by
    intro k
    unfold mtok mtokC
    rw [hq.caches k, hq.cp k, hq.pc k]
    simp
  exact (val_of_no_mtok hx h0).symm

/-! ### Fase 4: portare i valori delle cache a quello del parent -/

/-- Un passo interno è una `msi_rule`. -/
theorem acquire_M_aux0 {x y : MSIState n} {e : MSIInternalEvent n} (h : msi_step_internal x e y) :
    msi_rule n x y := ⟨e, h⟩

/-- Da uno stato quieto la cache `k` acquisisce `M` (richiesta, grant, presa: 3 passi): è in `M`
con il valore del parent, il resto è invariato. -/
theorem acquire_M {x : MSIState n} (hx : Good x) (hq : Quiet x) (k : Fin n) :
    ∃ f, trans_refl (msi_rule n) x f ∧ (f.caches k).state = Bstate.M
      ∧ (f.caches k).value = x.parent.value ∧ (f.caches k).queue_cp = 0 ∧ (f.caches k).queue_pc = 0
      ∧ (f.caches k).extqueue = (x.caches k).extqueue
      ∧ (∀ k', k' ≠ k → f.caches k' = x.caches k')
      ∧ f.parent.value = x.parent.value
      ∧ f.parent.shared_state = update_Fin k Bstate.M x.parent.shared_state
      ∧ (∀ k', f.parent.queue_cip k' = 0) ∧ (∀ k', f.parent.queue_pci k' = 0) := by
  have hkI := hq.caches k
  have hcp := hq.cp k
  have hpc := hq.pc k
  refine ⟨_, trans_refl.step
    (acquire_M_aux0 (msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.upgrade_from_I_rq _ hkI)))
    (trans_refl.step
      (acquire_M_aux0 (msi_step_internal.parent_upd_queue _ _ _ k
        (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ k ?h1 ?h2)))
      (trans_refl.step
        (acquire_M_aux0 (msi_step_internal.cache _ _ k _
          (cache_msi_step_internal.upgrade_from_I_rs _ x.parent.value ?h3 ?h4)))
        trans_refl.refl)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case h1 => simp [update_Fin_gss]
  case h2 => intro j; simpa using hq.rows j
  case h3 => simp [update_Fin_gss]
  case h4 => simp [update_Fin_gss, hkI]
  · simp [update_Fin_gss]
  · simp [update_Fin_gss]
  · simp [update_Fin_gss, hcp]
  · simp [update_Fin_gss, hpc]
  · simp [update_Fin_gss]
  · intro k' hkk
    simp [update_Fin_gso2 _ _ _ _ hkk]
  · simp
  · simp
  · intro k'
    by_cases hkk : k' = k
    · subst hkk; simp [update_Fin_gss, hcp]
    · simp [update_Fin_gso2 _ _ _ _ hkk, hq.cip k']
  · intro k'
    by_cases hkk : k' = k
    · subst hkk; simp [update_Fin_gss, hpc]
    · simp [update_Fin_gso2 _ _ _ _ hkk, hq.pci k']

/-- Una cache in `M` con le code vuote e il resto quieto torna quieta (rilascio, consumo: 2 passi),
tenendo il valore che ha e dandolo al parent. -/
theorem release_M {x : MSIState n} {k : Fin n} (hx : Good x)
    (hM : (x.caches k).state = Bstate.M) (hcp : (x.caches k).queue_cp = 0)
    (hpc : (x.caches k).queue_pc = 0) (hoth : ∀ k', k' ≠ k → (x.caches k').state = Bstate.I)
    (hrows : x.parent.shared_state = update_Fin k Bstate.M (fun _ => Bstate.I))
    (hcip : ∀ k', x.parent.queue_cip k' = 0) (hpci : ∀ k', x.parent.queue_pci k' = 0) :
    ∃ y, trans_refl (msi_rule n) x y ∧ Quiet y ∧ y.parent.value = (x.caches k).value
      ∧ (∀ k', (y.caches k').value = (x.caches k').value)
      ∧ (∀ k', (y.caches k').extqueue = (x.caches k').extqueue) := by
  have hsy := synced_of_good hx
  refine ⟨_, trans_refl.step
    (acquire_M_aux0 (msi_step_internal.cache _ _ k _
      (cache_msi_step_internal.rq_data_not_available _ hM)))
    (trans_refl.step
      (acquire_M_aux0 (msi_step_internal.parent_upd_queue _ _ _ k
        (parent_msi_step.downgrade_from_M_rq1 _ (x.caches k).value k ?h1)))
      trans_refl.refl), ?_, ?_, ?_, ?_⟩
  case h1 => simp [update_Fin_gss]
  · constructor
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hoth k' hkk]
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hcp]
      · have h0 : (x.caches k').queue_cp = 0 := by rw [← (hsy k').1]; exact hcip k'
        simp [update_Fin_gso2 _ _ _ _ hkk, h0]
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hpc]
      · have h0 : (x.caches k').queue_pc = 0 := by rw [← (hsy k').2]; exact hpci k'
        simp [update_Fin_gso2 _ _ _ _ hkk, h0]
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hrows]
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hcp]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hcip k']
    · intro k'
      by_cases hkk : k' = k
      · subst hkk; simp [update_Fin_gss, hpc]
      · simp [update_Fin_gso2 _ _ _ _ hkk, hpci k']
  · simp
  · intro k'
    by_cases hkk : k' = k
    · subst hkk; simp [update_Fin_gss]
    · simp [update_Fin_gso2 _ _ _ _ hkk]
  · intro k'
    by_cases hkk : k' = k
    · subst hkk; simp [update_Fin_gss]
    · simp [update_Fin_gso2 _ _ _ _ hkk]

theorem fix_step {x : MSIState n} {k : Fin n} (hx : Good x) (hq : Quiet x)
    (hk : (x.caches k).value ≠ x.parent.value) :
    ∃ y, trans_refl (msi_rule n) x y ∧ Quiet y ∧ y.parent.value = x.parent.value
      ∧ (y.caches k).value = x.parent.value
      ∧ (∀ k', k' ≠ k → (y.caches k').value = (x.caches k').value)
      ∧ (∀ k', (y.caches k').extqueue = (x.caches k').extqueue) := by
  obtain ⟨f, hxf, hfM, hfv, hfcp, hfpc, hfe, hoth, hpv, hrows, hcip, hpci⟩ := acquire_M hx hq k
  have hf : Good f := good_trans hx hxf
  have hoth' : ∀ k', k' ≠ k → (f.caches k').state = Bstate.I := by
    intro k' hkk
    rw [hoth k' hkk]
    exact hq.caches k'
  have hrows' : f.parent.shared_state = update_Fin k Bstate.M (fun _ => Bstate.I) := by
    rw [hrows]
    funext j
    by_cases hj : j = k
    · subst hj; simp [update_Fin_gss]
    · simp [update_Fin_gso2 _ _ _ _ hj, hq.rows j]
  obtain ⟨y, hfy, hqy, hyv, hyvals, hyext⟩ := release_M hf hfM hfcp hfpc hoth' hrows' hcip hpci
  refine ⟨y, trans_refl_trans hxf hfy, hqy, ?_, ?_, ?_, ?_⟩
  · rw [hyv, hfv]
  · rw [hyvals k, hfv]
  · intro k' hkk
    rw [hyvals k', hoth k' hkk]
  · intro k'
    rw [hyext k']
    by_cases hkk : k' = k
    · subst hkk; exact hfe
    · rw [hoth k' hkk]

theorem fix_all {x : MSIState n} (hx : Good x) (hq : Quiet x) :
    ∃ y, trans_refl (msi_rule n) x y ∧ Quiet y ∧ y.parent.value = x.parent.value
      ∧ (∀ k, (y.caches k).value = y.parent.value)
      ∧ (∀ k, (y.caches k).extqueue = (x.caches k).extqueue) := by
  suffices H : ∀ N, ∀ x : MSIState n, Good x → Quiet x → μ4 x x.parent.value ≤ N →
      ∃ y, trans_refl (msi_rule n) x y ∧ Quiet y ∧ y.parent.value = x.parent.value
        ∧ (∀ k, (y.caches k).value = y.parent.value)
        ∧ (∀ k, (y.caches k).extqueue = (x.caches k).extqueue) from
    H _ x hx hq le_rfl
  intro N
  induction N with
  | zero =>
    intro x hx hq hN
    have h0 : Finset.univ.sum (fun k => if (x.caches k).value = x.parent.value then 0 else 1) = 0 :=
      Nat.le_zero.mp hN
    refine ⟨x, trans_refl.refl, hq, rfl, ?_, fun _ => rfl⟩
    intro k
    have hk : (if (x.caches k).value = x.parent.value then 0 else 1) = 0 :=
      sum_eq_zero_iff_pointwise.mp h0 k
    by_contra hne
    simp [hne] at hk
  | succ N ih =>
    intro x hx hq hN
    by_cases h0 : μ4 x x.parent.value = 0
    · have h0' : Finset.univ.sum (fun k => if (x.caches k).value = x.parent.value then 0 else 1) = 0 :=
        h0
      refine ⟨x, trans_refl.refl, hq, rfl, ?_, fun _ => rfl⟩
      intro k
      have hk : (if (x.caches k).value = x.parent.value then 0 else 1) = 0 :=
        sum_eq_zero_iff_pointwise.mp h0' k
      by_contra hne
      simp [hne] at hk
    · have hpos : 0 < μ4 x x.parent.value := Nat.pos_of_ne_zero h0
      unfold μ4 at hpos
      obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hpos
      have hk2 : 0 < (if (x.caches k).value = x.parent.value then 0 else 1) := hk
      have hne : (x.caches k).value ≠ x.parent.value := by
        intro heq
        simp [heq] at hk2
      obtain ⟨y1, hxy1, hq1, hpv1, hval1, hoth1, hext1⟩ := fix_step hx hq hne
      have hy1 : Good y1 := good_trans hx hxy1
      have hlt : μ4 y1 y1.parent.value < μ4 x x.parent.value := by
        unfold μ4
        rw [hpv1]
        refine sum_lt_of_pointwise ?_ k ?_
        · intro k'
          show (if (y1.caches k').value = x.parent.value then 0 else 1)
            ≤ (if (x.caches k').value = x.parent.value then 0 else 1)
          by_cases hk' : k' = k
          · subst hk'
            simp [hval1]
          · rw [hoth1 k' hk']
        · show (if (y1.caches k).value = x.parent.value then 0 else 1)
            < (if (x.caches k).value = x.parent.value then 0 else 1)
          simp [hval1, hne]
      obtain ⟨y, hy1y, hqy, hpvy, hval, hext⟩ := ih y1 hy1 hq1 (by omega)
      refine ⟨y, trans_refl_trans hxy1 hy1y, hqy, hpvy.trans hpv1, hval, ?_⟩
      intro k'
      rw [hext k', hext1 k']

theorem canon_of_quiet {x : MSIState n} (hq : Quiet x)
    (hv : ∀ k, (x.caches k).value = x.parent.value) : x = canon x x.parent.value := by
  have hcaches : x.caches
      = fun k => ⟨Bstate.I, x.parent.value, 0, 0, (x.caches k).extqueue⟩ := by
    funext k
    have h1 := hq.caches k
    have h2 := hq.cp k
    have h3 := hq.pc k
    have h4 := hv k
    cases hck : x.caches k with
    | mk st v cp pc ext =>
      simp only [hck] at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
  have hparent : x.parent = ⟨x.parent.value, fun _ => Bstate.I, fun _ => 0, fun _ => 0⟩ := by
    have e1 : x.parent.shared_state = fun _ => Bstate.I := funext hq.rows
    have e2 : x.parent.queue_cip = fun _ => 0 := funext hq.cip
    have e3 : x.parent.queue_pci = fun _ => 0 := funext hq.pci
    cases hpp : x.parent with
    | mk pv rows cip pci =>
      simp only [hpp] at e1 e2 e3
      subst e1 e2 e3
      rfl
  have h : (⟨x.caches, x.parent⟩ : MSIState n) = canon x x.parent.value := by
    unfold canon
    rw [MSIState.mk.injEq]
    exact ⟨hcaches, hparent⟩
  exact h

/-- **Ogni stato raggiungibile arriva al suo stato canonico con passi interni.** -/
theorem reach_canon {x : MSIState n} (hx : Good x) :
    trans_refl (msi_rule n) x (canon x (val x)) := by
  obtain ⟨y, hxy, hq⟩ := reach_quiet hx
  have hy : Good y := good_trans hx hxy
  obtain ⟨z, hyz, hqz, hpz, hvz, hez⟩ := fix_all hy hq
  have hz : Good z := good_trans hy hyz
  have hcz : z = canon z z.parent.value := canon_of_quiet hqz hvz
  have hvalz : val z = z.parent.value := val_of_quiet hz hqz
  have hpath : trans_refl (msi_rule n) x z := trans_refl_trans hxy hyz
  have hcanon : canon z z.parent.value = canon x (val x) := by
    rw [← hvalz, canon_trans hx hpath]
  rw [← hcanon, ← hcz]
  exact hpath

/-! ## Il diamante -/

/-- **Confluenza dei passi interni sugli stati raggiungibili** (ipotesi (4) di
`ReachingStar.trace_inclusion`): il ricongiungimento è lo stato canonico di `a`, che è anche
quello di `b` e di `c`. -/
theorem msi_confluent :
    ReachingStar.has_diamond_property_on
      (fun i' => ReachingStar.reachable (msi_rule n) msi_step_external i' (default : MSIState n))
      (trans_refl (msi_rule n)) := by
  unfold ReachingStar.has_diamond_property_on
  intro a b c hR hac hab
  have ha : Good a := good_of_reach hR
  refine ⟨canon a (val a), ?_, ?_⟩
  · have := reach_canon (good_trans ha hac)
    rw [canon_trans ha hac] at this
    exact this
  · have := reach_canon (good_trans ha hab)
    rw [canon_trans ha hab] at this
    exact this

/-! ## La commutazione a meno di passi interni

Qui serve l'unico invariante del file, `SVal`: le copie `S` e i grant `rsS` portano il valore
del parent. Le viste non lo danno (non hanno valori) ed è necessario: in uno stato senza viste
cattive con una copia `S` a valore `5` e parent a `7`, la load servita da `S` risponde `5`, ma
dopo il rilascio interno della copia nessun cammino risponde più `5`. -/

structure SVal (x : MSIState n) : Prop where
  cacheS : ∀ k, (x.caches k).state = Bstate.S → (x.caches k).value = x.parent.value
  grantS : ∀ k v, PCEvent.rsS v ∈ (x.caches k).queue_pc → v = x.parent.value

theorem sval_default : SVal (default : MSIState n) := by
  constructor
  · intro k h
    exact Bstate.noConfusion h
  · intro k v h
    exact absurd h (Multiset.notMem_zero _)

/-- Un token `S` da qualche parte (`stok x k ≠ 0`) esclude ogni token `M`: la riga di `i` è `M`
solo se `k = i` (ma allora `stok = 0`) o `k ≠ i` (ma allora la riga di `k` è `I`). -/
theorem sval_step_aux0 {x : MSIState n} (hf : NoBadFacts x) {i k : Fin n} (hk : stok x k ≠ 0) :
    mtok x i = 0 := by
  cases hri : x.parent.shared_state i with
  | M =>
    exfalso
    by_cases hki : k = i
    · subst hki
      exact hk (hf.rowM _ hri).2
    · exact hk (hf.rowI k (hf.excl i k hri hki)).2
  | S => exact (hf.rowS i hri).2
  | I => exact (hf.rowI i hri).1

theorem sval_step_aux1 {x : MSIState n} (hf : NoBadFacts x) {i k : Fin n}
    (hS : (x.caches k).state = Bstate.S) : mtok x i = 0 :=
  sval_step_aux0 hf (fun h0 => (stok_zero_facts h0).1 hS)

theorem sval_step_aux2 {x : MSIState n} (hf : NoBadFacts x) {i k : Fin n} {v v' : Value}
    (hm : PCEvent.rsS v ∈ (x.caches k).queue_pc) (hmem : CPEvent.rsIμ v' ∈ (x.caches i).queue_cp) :
    False :=
  (mtok_zero_facts (sval_step_aux0 hf (fun h0 => (stok_zero_facts h0).2.1 v hm))).2.2 v' hmem

theorem sval_step_aux3 {f : Fin n → Multiset PCEvent} {i k : Fin n} {a m : PCEvent}
    (hm : m ∈ update_Fin i (a ::ₘ f i) f k) : m = a ∨ m ∈ f k := by
  by_cases hki : k = i
  · subst hki
    rw [update_Fin_gss] at hm
    exact Multiset.mem_cons.mp hm
  · rw [update_Fin_gso2 _ _ _ _ hki] at hm
    exact Or.inr hm

theorem sval_step {x y : MSIState n} {e : MSIInternalEvent n} (hf : NoBadFacts x) (hv : SVal x)
    (h : msi_step_internal x e y) : SVal y := by
  cases h with
  | cache cache' i e hc =>
    refine ⟨?_, ?_⟩
    · intro k hk
      change (update_Fin i cache' x.caches k).value = x.parent.value
      by_cases hki : k = i
      · rw [hki] at hk ⊢
        simp only [update_Fin_gss] at hk ⊢
        cases hc with
        | rq_data_not_available hM => simp at hk
        | rq_data_not_available1 hS => simp at hk
        | upgrade_from_I_rq hI => simp [hI] at hk
        | upgrade_from_I_rq1 hI => simp [hI] at hk
        | upgrade_from_I_rs v hmem hI => simp at hk
        | upgrade_from_I_rsS v hmem hI => exact hv.grantS i v hmem
        | downgrade_from_M_rs hmem hM => simp at hk
        | downgrade_from_M_rs1 hmem hS => simp at hk
      · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢
        exact hv.cacheS k hk
    · intro k v hm
      change v = x.parent.value
      by_cases hki : k = i
      · rw [hki] at hm
        simp only [update_Fin_gss] at hm
        cases hc with
        | rq_data_not_available hM => exact hv.grantS i v hm
        | rq_data_not_available1 hS => exact hv.grantS i v hm
        | upgrade_from_I_rq hI => exact hv.grantS i v hm
        | upgrade_from_I_rq1 hI => exact hv.grantS i v hm
        | upgrade_from_I_rs v' hmem hI => exact hv.grantS i v (Multiset.mem_of_mem_erase hm)
        | upgrade_from_I_rsS v' hmem hI => exact hv.grantS i v (Multiset.mem_of_mem_erase hm)
        | downgrade_from_M_rs hmem hM => exact hv.grantS i v (Multiset.mem_of_mem_erase hm)
        | downgrade_from_M_rs1 hmem hS => exact hv.grantS i v (Multiset.mem_of_mem_erase hm)
      · simp only [update_Fin_gso2 _ _ _ _ hki] at hm
        exact hv.grantS k v hm
  | parent_upd_queue parent' e i hp =>
    have hcp := (hf.synced i).1
    refine ⟨?_, ?_⟩
    · intro k hk
      change (update_Fin i _ x.caches k).value = parent'.value
      by_cases hki : k = i
      · rw [hki] at hk ⊢
        simp only [update_Fin_gss] at hk ⊢
        have hm0 : ∀ v, CPEvent.rsIμ v ∉ x.parent.queue_cip i := by
          intro v hmem
          rw [hcp] at hmem
          exact (mtok_zero_facts (sval_step_aux1 hf hk)).2.2 v hmem
        cases hp with
        | downgrade_from_M_rq1 v _ hmem => exact absurd hmem (hm0 v)
        | downgrade_from_M_rq2 _ hmem => exact hv.cacheS i hk
        | upgrade_to_M_data_avilable_rq1 _ hmem hall => exact hv.cacheS i hk
        | upgrade_to_M_data_avilable_rq2 _ hmem hI hall => exact hv.cacheS i hk
        | upgrade_to_M_invalid_all j _ hmem hM => exact hv.cacheS i hk
        | upgrade_to_M_invalid_all1 j _ hmem hS => exact hv.cacheS i hk
        | upgrade_to_M_invalid_all2 j _ hmem hne hS => exact hv.cacheS i hk
        | upgrade_to_M_invalid_all3 j _ hmem hM => exact hv.cacheS i hk
      · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢
        have hm0 : ∀ v, CPEvent.rsIμ v ∉ x.parent.queue_cip i := by
          intro v hmem
          rw [hcp] at hmem
          exact (mtok_zero_facts (sval_step_aux1 hf hk)).2.2 v hmem
        cases hp with
        | downgrade_from_M_rq1 v _ hmem => exact absurd hmem (hm0 v)
        | downgrade_from_M_rq2 _ hmem => exact hv.cacheS k hk
        | upgrade_to_M_data_avilable_rq1 _ hmem hall => exact hv.cacheS k hk
        | upgrade_to_M_data_avilable_rq2 _ hmem hI hall => exact hv.cacheS k hk
        | upgrade_to_M_invalid_all j _ hmem hM => exact hv.cacheS k hk
        | upgrade_to_M_invalid_all1 j _ hmem hS => exact hv.cacheS k hk
        | upgrade_to_M_invalid_all2 j _ hmem hne hS => exact hv.cacheS k hk
        | upgrade_to_M_invalid_all3 j _ hmem hM => exact hv.cacheS k hk
    · intro k v hm
      change v = parent'.value
      have hm' : PCEvent.rsS v ∈ parent'.queue_pci k := by
        by_cases hki : k = i
        · subst hki
          simpa only [update_Fin_gss] using hm
        · rw [(parent_step_local hp k hki).2.1, (hf.synced k).2]
          simpa only [update_Fin_gso2 _ _ _ _ hki] using hm
      clear hm
      cases hp with
      | downgrade_from_M_rq1 v' _ hmem =>
        exact (sval_step_aux2 hf (by rw [← (hf.synced k).2]; exact hm')
          (by rw [← hcp]; exact hmem)).elim
      | downgrade_from_M_rq2 _ hmem =>
        exact hv.grantS k v (by rw [← (hf.synced k).2]; exact hm')
      | upgrade_to_M_data_avilable_rq1 _ hmem hall =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · cases h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)
      | upgrade_to_M_data_avilable_rq2 _ hmem hI hall =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · exact PCEvent.rsS.inj h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)
      | upgrade_to_M_invalid_all j _ hmem hM =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · cases h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)
      | upgrade_to_M_invalid_all1 j _ hmem hS =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · cases h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)
      | upgrade_to_M_invalid_all2 j _ hmem hne hS =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · cases h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)
      | upgrade_to_M_invalid_all3 j _ hmem hM =>
        try dsimp only at hm'
        rcases sval_step_aux3 hm' with h | h
        · cases h
        · exact hv.grantS k v (by rw [← (hf.synced k).2]; exact h)

theorem sval_step_ext {x y : MSIState n} {e : MSIExternalEvent n} (hf : NoBadFacts x) (hv : SVal x)
    (h : msi_step_external x e y) : SVal y := by
  cases h with
  | cache e cache' i hc =>
    refine ⟨?_, ?_⟩
    · intro k hk
      change (update_Fin i cache' x.caches k).value = x.parent.value
      by_cases hki : k = i
      · rw [hki] at hk ⊢
        simp only [update_Fin_gss] at hk ⊢
        cases hc with
        | ld_rq => exact hv.cacheS i hk
        | st_rq v => exact hv.cacheS i hk
        | ld_rq_data_available1 rst hrq hS => exact hv.cacheS i hk
        | ld_rq_data_available rst hrq hM => exact hv.cacheS i hk
        | st_rq_M_state v rst hrq hM => simp [hM] at hk
      · simp only [update_Fin_gso2 _ _ _ _ hki] at hk ⊢
        exact hv.cacheS k hk
    · intro k v hm
      change v = x.parent.value
      by_cases hki : k = i
      · rw [hki] at hm
        simp only [update_Fin_gss] at hm
        cases hc <;> exact hv.grantS i v hm
      · simp only [update_Fin_gso2 _ _ _ _ hki] at hm
        exact hv.grantS k v hm

theorem sval_of_reach_aux1 {x y : MSIState n} (hx : Reach x) (hv : SVal x)
    (h : trans_refl (msi_rule n) x y) : SVal y := by
  induction h with
  | refl => exact hv
  | step hr _ ih =>
    obtain ⟨e, he⟩ := hr
    exact ih (reach_step hx he) (sval_step (noBadFacts_of_reach hx) hv he)

theorem sval_of_reach {x : MSIState n} (hx : Reach x) : SVal x := by
  suffices H : Reach x ∧ SVal x from H.2
  unfold Reach ReachingStar.reachable at hx
  obtain ⟨l, hl⟩ := hx
  induction hl with
  | refl => exact ⟨reach_default, sval_default⟩
  | step_int l s' s'' _ hpath ih =>
    exact ⟨reach_trans ih.1 hpath, sval_of_reach_aux1 ih.1 ih.2 hpath⟩
  | step_ext l s' s'' e _ hstep ih =>
    exact ⟨reach_step_ext ih.1 hstep, sval_step_ext (noBadFacts_of_reach ih.1) ih.2 hstep⟩

/-- Una copia `S` vale `val` (nessun token `M` in giro, quindi `val` è il parent). -/
theorem val_of_S {x : MSIState n} {k : Fin n} (hx : Good x) (hv : SVal x)
    (hS : (x.caches k).state = Bstate.S) : (x.caches k).value = val x := by
  have hf := noBadFacts_of_good hx
  rw [hv.cacheS k hS]
  refine val_of_no_mtok hx (fun i => ?_)
  have hrowk := hf.cacheS k hS
  cases hri : x.parent.shared_state i with
  | M =>
    exfalso
    by_cases hki : k = i
    · rw [hki, hri] at hrowk
      cases hrowk
    · have := hf.excl i k hri hki
      rw [hrowk] at this
      cases this
  | S => exact (hf.rowS i hri).2
  | I => exact (hf.rowI i hri).1

/-- Una copia `M` vale `val`. -/
theorem val_of_M {x : MSIState n} {k : Fin n} (hx : Good x) (hM : (x.caches k).state = Bstate.M) :
    (x.caches k).value = val x :=
  (lvm_val (noBadFacts_of_good hx)).cacheM k hM

/-- Da uno stato raggiungibile si arriva con passi interni a uno stato in cui la cache `k` è in
`M` con valore `val`; le `extqueue` non cambiano. -/
theorem reach_M {x : MSIState n} (hx : Good x) (k : Fin n) :
    ∃ f, trans_refl (msi_rule n) x f ∧ (f.caches k).state = Bstate.M ∧ (f.caches k).value = val x
      ∧ ∀ k', (f.caches k').extqueue = (x.caches k').extqueue := by
  obtain ⟨y, hxy, hq⟩ := reach_quiet hx
  have hy : Good y := good_trans hx hxy
  obtain ⟨f, hyf, hfM, hfv, _, _, hfe, hoth, _, _, _, _⟩ := acquire_M hy hq k
  refine ⟨f, trans_refl_trans hxy hyf, hfM, ?_, ?_⟩
  · rw [hfv, ← val_of_quiet hy hq, val_trans hx hxy]
  · intro k'
    by_cases hk : k' = k
    · subst hk; rw [hfe, ext_trans hxy]
    · rw [hoth k' hk, ext_trans hxy]

/-- Un passo esterno che non tocca stato, valore e code della cache `k` conserva `LVM`. -/
theorem val_ext_aux1 {x : MSIState n} {m : Value} {k : Fin n} {c' : CacheState}
    (hl : LVM x m) (hs : c'.state = (x.caches k).state) (hv : c'.value = (x.caches k).value)
    (hcp : c'.queue_cp = (x.caches k).queue_cp) (hpc : c'.queue_pc = (x.caches k).queue_pc) :
    LVM { x with caches := update_Fin k c' x.caches,
                 parent.queue_cip := update_Fin k c'.queue_cp x.parent.queue_cip,
                 parent.queue_pci := update_Fin k c'.queue_pc x.parent.queue_pci } m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k' hM
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hM ⊢
      rw [hv]
      exact hl.cacheM _ (hs ▸ hM)
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hM ⊢
      exact hl.cacheM k' hM
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      rw [hpc] at hmem
      exact hl.grantM _ v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hl.grantM k' v hmem
  · intro k' v hmem
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at hmem
      rw [hcp] at hmem
      exact hl.release _ v hmem
    · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
      exact hl.release k' v hmem
  · intro h0
    apply hl.parent
    intro k'
    have := h0 k'
    unfold mtok mtokC at this ⊢
    by_cases hk : k' = k
    · subst hk
      simp only [update_Fin_gss] at this
      rw [hs, hpc, hcp] at this
      exact this
    · simp only [update_Fin_gso2 _ _ _ _ hk] at this
      exact this

/-- Il valore logico dopo un passo esterno: invariato, salvo una store servita, che lo pone al
valore scritto. -/
theorem val_ext {x y : MSIState n} {ev : Event} {k : Fin n} (hx : Good x)
    (h : msi_step_external x (.cache ev k) y) :
    (ev ≠ Event.st_rs → val y = val x) ∧
    (ev = Event.st_rs → ∃ v rst, (x.caches k).extqueue.rq = Event.st_rq v :: rst ∧ val y = v) := by
  have hf := noBadFacts_of_good hx
  have hf' := noBadFacts_of_good (good_step_ext hx h)
  have hl := lvm_val hf
  cases h
  rename_i c' hc'
  cases hc' with
  | ld_rq =>
    exact ⟨fun _ => val_eq_of_lvm hf' (val_ext_aux1 hl rfl rfl rfl rfl), fun heq => by cases heq⟩
  | st_rq v =>
    exact ⟨fun _ => val_eq_of_lvm hf' (val_ext_aux1 hl rfl rfl rfl rfl), fun heq => by cases heq⟩
  | ld_rq_data_available1 rst hrq hS =>
    exact ⟨fun _ => val_eq_of_lvm hf' (val_ext_aux1 hl rfl rfl rfl rfl), fun heq => by cases heq⟩
  | ld_rq_data_available rst hrq hM =>
    exact ⟨fun _ => val_eq_of_lvm hf' (val_ext_aux1 hl rfl rfl rfl rfl), fun heq => by cases heq⟩
  | st_rq_M_state v rst hrq hM =>
    refine ⟨fun hne => absurd rfl hne, fun _ => ⟨v, rst, hrq, ?_⟩⟩
    apply val_eq_of_lvm hf'
    -- la cache `k` è in `M`: la sua riga è `M`, ha un solo token `M`, nessun token `S`,
    -- e tutte le altre cache non hanno token
    have hrow : x.parent.shared_state k = Bstate.M := hf.cacheM k hM
    obtain ⟨hm1, hs0⟩ := hf.rowM k hrow
    have hother : ∀ k', k' ≠ k → mtok x k' = 0 ∧ stok x k' = 0 :=
      fun k' hne => hf.rowI k' (hf.excl k k' hrow hne)
    have hcnt : (x.caches k).queue_pc.countP (fun e => isGrantM e = true) = 0 ∧
        (x.caches k).queue_cp.countP (fun e => isReleaseM e = true) = 0 := by
      unfold mtok mtokC at hm1; rw [hM, if_pos rfl] at hm1; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k' hM'
      by_cases hk : k' = k
      · subst hk; simp only [update_Fin_gss]
      · exfalso
        simp only [update_Fin_gso2 _ _ _ _ hk] at hM'
        exact (mtok_zero_facts (hother k' hk).1).1 hM'
    · intro k' w hmem
      exfalso
      by_cases hk : k' = k
      · subst hk
        simp only [update_Fin_gss] at hmem
        exact (Multiset.countP_eq_zero.mp hcnt.1) _ hmem rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
        exact (mtok_zero_facts (hother k' hk).1).2.1 w hmem
    · intro k' w hmem
      exfalso
      by_cases hk : k' = k
      · subst hk
        simp only [update_Fin_gss] at hmem
        exact (Multiset.countP_eq_zero.mp hcnt.2) _ hmem rfl
      · simp only [update_Fin_gso2 _ _ _ _ hk] at hmem
        exact (mtok_zero_facts (hother k' hk).1).2.2 w hmem
    · intro hall
      exfalso
      have := hall k
      unfold mtok mtokC at this
      simp [update_Fin_gss, hM] at this

/-- Due stati raggiungibili con lo stesso valore logico e le stesse `extqueue` si ricongiungono
nello stato canonico comune. -/
theorem join_of_val {c d : MSIState n} (hc : Good c) (hd : Good d) (hval : val c = val d)
    (hext : ∀ k, (c.caches k).extqueue = (d.caches k).extqueue) :
    ∃ j, trans_refl (msi_rule n) c j ∧ trans_refl (msi_rule n) d j := by
  refine ⟨canon c (val c), reach_canon hc, ?_⟩
  rw [canon_ext hext, hval]
  exact reach_canon hd

/-- **Commutazione a meno di passi interni sugli stati raggiungibili** (ipotesi (5) di
`ReachingStar.trace_inclusion`). Richieste: `b' = b`, `d` = `b` più la richiesta, `j` lo stato
canonico. Risposte: da `b` si va a uno stato con la cache in `M` e valore `val` (`reach_M`), la
richiesta è ancora in testa (le `extqueue` non cambiano), la risposta ha lo stesso valore che in
`c` (`val_of_S`, `val_of_M`), e `j` è lo stato canonico comune (`join_of_val`). -/
theorem msi_commutes_upto :
    ReachingStar.commutes_method_rule_upto_on
      (fun i' => ReachingStar.reachable (msi_rule n) msi_step_external i' (default : MSIState n))
      msi_step_external (msi_rule n) := by
  unfold ReachingStar.commutes_method_rule_upto_on
  intro a b c e hR hab hac
  have hRa : Reach a := hR
  have ha : Good a := good_of_reach hR
  have hb : Good b := good_trans ha hab
  have hextab := ext_trans hab
  have hvab : val b = val a := val_trans ha hab
  have hac' := hac
  cases e with
  | cache ev k =>
  cases hac
  rename_i c' hc'
  cases hc' with
  | ld_rq =>
    -- richiesta: `b' = b`, `d` = `b` più la richiesta, `j` lo stato canonico
    have hd := msi_step_external.cache b _ _ k (cache_msi_step.ld_rq (b.caches k))
    have hc : Good _ := good_step_ext ha hac'
    have hd' : Good _ := good_step_ext hb hd
    have hvc := (val_ext ha hac').1 (by intro h; cases h)
    have hvd := (val_ext hb hd).1 (by intro h; cases h)
    obtain ⟨j, hcj, hdj⟩ := join_of_val hc hd' (by rw [hvc, hvd, hvab])
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextab]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextab k').symm)
    exact ⟨b, _, j, trans_refl.refl, hd, hcj, hdj⟩
  | st_rq v =>
    have hd := msi_step_external.cache b _ _ k (cache_msi_step.st_rq (b.caches k) v)
    have hc : Good _ := good_step_ext ha hac'
    have hd' : Good _ := good_step_ext hb hd
    have hvc := (val_ext ha hac').1 (by intro h; cases h)
    have hvd := (val_ext hb hd).1 (by intro h; cases h)
    obtain ⟨j, hcj, hdj⟩ := join_of_val hc hd' (by rw [hvc, hvd, hvab])
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextab]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextab k').symm)
    exact ⟨b, _, j, trans_refl.refl, hd, hcj, hdj⟩
  | ld_rq_data_available1 rst hrq hS =>
    -- risposta a una load (da `S`): da `b` si riacquisisce `M` e si serve la stessa richiesta
    have hva : (a.caches k).value = val a := val_of_S ha (sval_of_reach hRa) hS
    obtain ⟨f, hbf, hfM, hfv, hfext⟩ := reach_M hb k
    have hf : Good f := good_trans hb hbf
    have hvbf : val f = val a := by rw [val_trans hb hbf, hvab]
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfv' : (f.caches k).value = (a.caches k).value := by rw [hfv, hvab, hva]
    have hfrq : (f.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hextaf k]; exact hrq
    have hd := msi_step_external.cache f _ _ k
      (cache_msi_step.ld_rq_data_available (f.caches k) rst hfrq hfM)
    rw [hfv'] at hd
    have hc : Good _ := good_step_ext ha hac'
    have hd' : Good _ := good_step_ext hf hd
    have hvc := (val_ext ha hac').1 (by intro h; cases h)
    have hvd := (val_ext hf hd).1 (by intro h; cases h)
    obtain ⟨j, hcj, hdj⟩ := join_of_val hc hd' (by rw [hvc, hvd, hvbf])
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩
  | ld_rq_data_available rst hrq hM =>
    -- risposta a una load (da `M`)
    have hva : (a.caches k).value = val a := val_of_M ha hM
    obtain ⟨f, hbf, hfM, hfv, hfext⟩ := reach_M hb k
    have hf : Good f := good_trans hb hbf
    have hvbf : val f = val a := by rw [val_trans hb hbf, hvab]
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfv' : (f.caches k).value = (a.caches k).value := by rw [hfv, hvab, hva]
    have hfrq : (f.caches k).extqueue.rq = Event.ld_rq :: rst := by rw [hextaf k]; exact hrq
    have hd := msi_step_external.cache f _ _ k
      (cache_msi_step.ld_rq_data_available (f.caches k) rst hfrq hfM)
    rw [hfv'] at hd
    have hc : Good _ := good_step_ext ha hac'
    have hd' : Good _ := good_step_ext hf hd
    have hvc := (val_ext ha hac').1 (by intro h; cases h)
    have hvd := (val_ext hf hd).1 (by intro h; cases h)
    obtain ⟨j, hcj, hdj⟩ := join_of_val hc hd' (by rw [hvc, hvd, hvbf])
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩
  | st_rq_M_state v rst hrq hM =>
    -- risposta a una store: da `b` si riacquisisce `M` e si serve la stessa richiesta; il nuovo
    -- valore logico è `v` da entrambe le parti
    obtain ⟨f, hbf, hfM, _, hfext⟩ := reach_M hb k
    have hf : Good f := good_trans hb hbf
    have hextaf : ∀ k', (f.caches k').extqueue = (a.caches k').extqueue :=
      fun k' => (hfext k').trans (hextab k')
    have hfrq : (f.caches k).extqueue.rq = Event.st_rq v :: rst := by rw [hextaf k]; exact hrq
    have hd := msi_step_external.cache f _ _ k
      (cache_msi_step.st_rq_M_state (f.caches k) v rst hfrq hfM)
    have hc : Good _ := good_step_ext ha hac'
    have hd' : Good _ := good_step_ext hf hd
    obtain ⟨v1, rst1, hrq1, hvc⟩ := (val_ext ha hac').2 rfl
    obtain ⟨v2, rst2, hrq2, hvd⟩ := (val_ext hf hd).2 rfl
    have hv1 : v1 = v := by
      rw [hrq] at hrq1
      exact (Event.st_rq.inj (List.cons.inj hrq1).1).symm
    have hv2 : v2 = v := by
      rw [hfrq] at hrq2
      exact (Event.st_rq.inj (List.cons.inj hrq2).1).symm
    obtain ⟨j, hcj, hdj⟩ := join_of_val hc hd' (by rw [hvc, hvd, hv1, hv2])
      (by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp only [update_Fin_gss]; rw [hextaf]
        · simp only [update_Fin_gso2 _ _ _ _ hk]; exact (hextaf k').symm)
    exact ⟨f, _, j, hbf, hd, hcj, hdj⟩

end MSIBag
