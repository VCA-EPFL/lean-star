# Star

## Bluespec module proofs

This is an explanation of what happens in [mkBluealloc\_refines.lean](/Star/Bluespec/Example/mkBluealloc_refines.lean).

First we define types that refer to each rule of the implementation and each method of the implementation and the
specification.

```lean4
inductive RuleTag where
| RL_do_read_index
| RL_do_write_index
| RL_do_free_lookup
| RL_do_free_read
| RL_do_free_write
| RL_do_alloc_prefetch
| RL_do_alloc_wait

inductive Methods : Type where
| alloc
| free
| write_req
| read_req
| read_resp
```

We then define the Bluespec modules for the implementation and the specification as follows, assuming that `Spec.State`
refers to the abstract specification state and `Impl.state` refers to the implementation state.  The current
`Bluespec.Module` structure separates internal rules from externally visible methods; see
[Queue.lean](/Star/Bluespec/Queue.lean) for a small complete example.

```lean4
def SpecModule : Bluespec.Module Empty Methods where
  State := Spec.State
  rules := Empty.casesOn _
  methods
    | .alloc => ofAVMethod0 Spec.meth_alloc Spec.meth_RDY_alloc
    | .free => ofAVMethod1 Spec.meth_free Spec.meth_RDY_free
    | .write_req => ofAVMethod2 Spec.meth_write_req Spec.meth_RDY_write_req
    | .read_req => ofAVMethod1 Spec.meth_read_req Spec.meth_RDY_read_req
    | .read_resp => ofAVMethod0 Spec.meth_read_resp Spec.meth_RDY_read_resp

def ImplModule : Bluespec.Module RuleTag Methods where
  State := Impl.state
  rules
    | .RL_do_read_index => ofRule rule_RL_do_read_index
    | .RL_do_write_index => ofRule rule_RL_do_write_index
    | .RL_do_free_lookup => ofRule rule_RL_do_free_lookup
    | .RL_do_free_read => ofRule rule_RL_do_free_read
    | .RL_do_free_write => ofRule rule_RL_do_free_write
    | .RL_do_alloc_prefetch => ofRule rule_RL_do_alloc_prefetch
    | .RL_do_alloc_wait => ofRule rule_RL_do_alloc_wait
  methods
    | .alloc => ofAVMethod0 meth_alloc meth_RDY_alloc
    | .free => ofAVMethod1 meth_free meth_RDY_free
    | .write_req => ofAVMethod2 meth_write_req meth_RDY_write_req
    | .read_req => ofAVMethod1 meth_read_req meth_RDY_read_req
    | .read_resp => ofAVMethod0 meth_read_resp meth_RDY_read_resp
```

This is just a mapping from rules and methods to their implementations, using `ofRule` to lift rules and `ofAVMethodN`
to lift methods with `N` number of arguments.  For methods, two arguments are expected for the lifting: the actual
method (i.e. `meth_alloc`) and the ready predicate of the method (i.e. `meth_RDY_alloc`).  The event footprint is
supplied later through `Module.getMethod`.

It is often useful to register small case lemmas for `grind`, following the pattern in `Queue.lean`:

```lean4
@[local grind →] theorem ImplModule.get_method_cases :
  ImplModule.getMethod i e i' →
  (∃ (addr : BitVec 16) (data : BitVec 32) (v : unit_),
      e.1 = .write_req ∧ e.2 = Footprint.arg2 addr data v) ∨
    -- one disjunct per other method
    True := by
  -- unfold the method table and let `grind` extract the footprint equality
  sorry

@[local grind →] theorem ImplModule.get_rule_cases :
  ImplModule.getARule i i' →
  (∃ r, ImplModule.getRule r i i') := by
  intro h
  exact h
```

Then, we need to generate the following style of lemmas:

```lean4
/-- Rule/rule commuting -/
theorem commutes_RL_do_read_index_RL_do_write_index {a b c : ImplModule.State} :
  ImplModule.getRule RuleTag.RL_do_read_index a c →
  ImplModule.getRule RuleTag.RL_do_write_index a b →
  ∃ d, Relation.ReflTransGen ImplModule.getARule c d ∧ Relation.ReflTransGen ImplModule.getARule b d := by sorry

-- Generate one for each rule/rule pair
-- ...

/-- Method/rule commuting -/
theorem reconverge_RL_do_alloc_prefetch_write_req (s s' s'': state) (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) :
  ImplModule.getRule .RL_do_alloc_prefetch s s' →
  ImplModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'' →
  ∃ s''',
    ImplModule.getMethod s' ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s'''
    ∧ ImplModule.getRule .RL_do_alloc_prefetch s'' s''' := by sorry
    
-- Generate one for each method/rule pair
-- ...
```

And finally, for the lemmas between the implementation and the spec for a specific `flushed` (i.e. `phi_0`) relation:

```lean4
def flushed : ImplModule.State → SpecModule.State → Prop := M_mkBluealloc.WeakSim.phi0
```

We then need the following style of lemmas to hold.  These only need to be defined once per method (i.e. the same method
is executed by the spec and the implementation).

```lean4
/-- Flush indistinguishability -/

theorem flush_indistinguishable_write_req (i i' : ImplModule.State) (s : SpecModule.State)
        (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) : 
  flushed i s ->
  ImplModule.getMethod i ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ i' ->
  ∃ s', SpecModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s' := by sorry

-- Generate one for each method
-- ...

/-- Can reach flush again after executing method -/

theorem reach_flush_again_write_req (i i' : ImplModule.State) (s s' : SpecModule.State)
        (write_req_addr : BitVec 16) (write_req_data : BitVec 32) (v : unit_) : 
  flushed i s ->
  ImplModule.getMethod i ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ i' ->
  SpecModule.getMethod s ⟨.write_req, Footprint.arg2 write_req_addr write_req_data v⟩ s' ->
  ∃ i'', Relation.ReflTransGen ImplModule.getARule i' i'' ∧ flushed i'' s' := by sorry
  
-- Generate one for each method
-- ...

/-- Flush reaches flush again after internal rule -/

theorem flush_reaches_flush_RL_do_read_index (i i' : ImplModule.State) (s : SpecModule.State) :
  flushed i s -> ImplModule.getRule .RL_do_read_index i i' -> flushed i' s := by sorry
  
-- Generate one for each rule.
-- ...
```
