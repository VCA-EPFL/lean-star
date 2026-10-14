import StarExperimental.MSI_final_def
import StarExperimental.MSI_flush_proof

/-!
# `MSI_final`: la relazione di flush

La relazione tra uno stato di `MSI_final` e uno stato dello spec sequenziale `SeqState`
(`MSI_flush_proof.lean`). È la **più piccola** con cui le quattro ipotesi di `ReachingStar.trace_inclusion`
(`relation_init`, `relation_flush`, `relation_method_int`, `relation_flush_method_int`) si dimostrano:

* `Reach i`: lo stato è raggiungibile. Senza, le ipotesi di ARS parlerebbero di stati arbitrari (due
  cache in `M`, ...) e la clausola sui valori non si conserverebbe. È ciò che permette di usare
  l'irraggiungibilità delle viste al posto di un invariante scritto a mano.
* le `extqueue` coincidono: `seq_step` guarda la testa di `rq`, e un metodo abilitato
  nell'implementazione deve esserlo anche nello spec.
* **ogni copia viva del valore è la memoria dello spec**. Il valore può stare in cinque posti, e
  ciascuno è letto da qualcuno: le cache in `S`/`M` (dai metodi di load), i grant `rsM`/`rsS` (dalla
  cache che li riceve), il rilascio `rsIμ` (dal parent che lo consuma), `parent.value` (dai grant,
  quando nessuna riga è `M`). Nessuna delle cinque clausole si può togliere: la relazione smetterebbe
  di essere conservata dal passo che legge quel posto.

Nessuna condizione di forma (code vuote, cache a `I`, messaggi in volo): la relazione è conservata da
ogni passo interno, quindi le ipotesi di ARS valgono con zero passi interni (`i'' := i'`).

Le code sono citate dal lato cache (`queue_pc`, `queue_cp`); il lato parent (`queue_pci`, `queue_cip`)
ne è la copia (`MSIView.synced`, vera su ogni stato raggiungibile).
-/

open THEORY Relation

namespace MSIFinal

variable {n : Nat}

/-- La relazione di flush di `MSI_final`. -/
def flush (i : MSIState n) (s : SeqState n) : Prop :=
  -- stato raggiungibile
  Reach i ∧
  -- stesse code esterne
  (∀ k, (i.caches k).extqueue = s.extqueue k) ∧
  -- una cache in `S` o `M` ha il valore della memoria
  (∀ k, (i.caches k).state ≠ Bstate.I → (i.caches k).value = s.memory) ∧
  -- un grant `rsM v` in volo porta il valore della memoria
  (∀ k v, PCEvent.rsM v ∈ (i.caches k).queue_pc → v = s.memory) ∧
  -- un grant `rsS v` in volo porta il valore della memoria
  (∀ k v, PCEvent.rsS v ∈ (i.caches k).queue_pc → v = s.memory) ∧
  -- un rilascio `rsIμ v` in volo porta il valore della memoria
  (∀ k v, CPEvent.rsIμ v ∈ (i.caches k).queue_cp → v = s.memory) ∧
  -- se nessuna riga è `M`, il parent ha il valore della memoria
  ((∀ k, i.parent.shared_state k ≠ Bstate.M) → i.parent.value = s.memory)

end MSIFinal
