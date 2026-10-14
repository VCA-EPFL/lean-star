# Star

Lean 4 formalization of refinement by flushing: an implementation with internal steps refines a specification
when it is enough to relate the two systems in the implementation's *flushed* states, those in which no internal
step is possible.

The repository contains the abstract theory and two case studies:

* **Theory** (`Star/Theory`): the flush-based simulation theorem, trace inclusion, and a completeness result.
* **Join–join rewrite** (`Star/Evaluation/join_join.lean`): the re-association of two dataflow `join` components,
  proved from a flush relation made of two equations.
* **Bluespec allocator** (`Star/Evaluation/Allocator`): a hardware allocator written in Bluespec SystemVerilog,
  translated to Lean, and proved to refine an abstract allocator specification from reset.

No proof uses `sorry` or `admit`.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.29.0`) is pinned in
`lean-toolchain`, and Mathlib (`v4.29.0`) in `lakefile.toml`.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build           # builds every module under Star/
```

The default target `StarCore` (glob `Star.+`) includes every Lean file under `Star/`. Some files end with `#print axioms` for their main
theorem, so the build output lists the axioms each result depends on. `Queue.lean` checks its axioms with
`#guard_msgs`.

## Repository layout

```
Star/
├── Theory/
│   ├── ARS.lean            theory: flush relations, φ_ind, enough_star(_on/_upto), trace inclusion
│   ├── ARS2.lean           earlier version of the theory, used by the allocator case study
│   └── THE_THEOREM1.lean   completeness: every refinement yields a flush-based one
└── Evaluation/
    ├── join_join.lean      join–join rewrite: rhs ⊑ lhs
    └── Allocator/
        ├── Basic.lean      Bluespec modules as transition systems; StructuredRefinement
        ├── HVector.lean    heterogeneous vectors (method arguments)
        ├── Queue.lean      small complete example: two-list queue ⊑ one-list queue
        ├── Example/
        │   ├── Bluealloc.bsv               Bluespec source of the allocator
        │   ├── Bluealloc_types.lean        translated enumerations
        │   ├── mkBluealloc.lean            translated implementation
        │   └── mkBluealloc_refines.lean    specification and refinement proof
        └── Lib/
            ├── BluespecPrelude.lean        runtime support for translated Bluespec code
            ├── BluespecVerification.lean   verification helpers
            ├── mkSimpleBRAM2.lean          model of the dual-port BRAM used by the allocator
            ├── mkSimpleBRAM.lean           model of the single-port BRAM, not used by the allocator
            ├── mkBypassFIFO.lean           model of the bypass FIFO, not used by the allocator
            ├── Vector_types.lean           empty placeholder for the BSV Vector library, not used
            └── BluespecPrelude.mlw         Why3 version of the prelude, not part of the Lean build
```

## Theory (`Star/Theory`)

Everything is stated over abstract reduction systems, in namespace `ReachingStar` (except the completeness result, in
namespace `the_theorem1`). An implementation has states `A`,
internal rules `rule : Rule A` (`A → A → Prop`) and labelled methods `method_i : Method A E`
(`A → E → A → Prop`). A specification has states `B` and methods `method_s : Method B E` only. `trans_refl rule`
is the reflexive-transitive closure of the rules, written `→*` below.

The user provides a **flush relation** `flush : A → B → Prop`, meant to hold only on flushed implementation states.
The theory closes it backwards under internal steps into the inductive relation **`φ_ind flush rule`**:
`φ_ind i s` holds when the rules take `i` to a state flushed with respect to `s`. The main theorems show that
`φ_ind` is a simulation, given:

| Obligation | Meaning |
|---|---|
| `relation_flush` | after internal steps from a flushed state, further internal steps reach a flushed state again |
| `relation_method` / `relation_method_int` | a method the implementation can take (in a flushed state, or after internal steps from one) can also be taken by the specification |
| `relation_flush_method` / `relation_flush_method_int` | after the same method on both sides, internal steps bring the implementation back to a flushed state |
| `has_diamond_property (trans_refl rule)` | the internal rules are confluent |
| `commutes_weakly_method_rule` | a method commutes with internal steps |

Main results, all in [`ARS.lean`](Star/Theory/ARS.lean):

| Lean name | Statement |
|---|---|
| `ReachingStar.enough_star` | `φ_ind` is a simulation: every implementation run (`star_extend`) is matched by a specification run (`star`) with the same labels, under the obligations above, required on all states |
| `ReachingStar.enough_star_on` | the same, with confluence and commutation required only on a set of states `R` closed under steps |
| `ReachingStar.enough_star_upto` | the most general form: in addition, methods commute with internal steps only *up to* further internal steps (`commutes_method_rule_upto_on`), with the `_int` obligations |
| `ReachingStar.trace_inclusion` | every trace of the implementation from `init_i` is a trace of the specification from `init_s`, from `enough_star_upto` with `R` the reachable states and `relation_init` (`flush init_i init_s`: the initial states are related by the flush relation) |
| `ReachingStar.trace_inclusion_strong` | the same with immediate commutation (`commutes_weakly_method_rule_on`) and the plain `relation_method` / `relation_flush_method`, via `enough_star_on` |
| `ReachingStar.newmans_lemma` | local confluence and strong normalization give confluence |

[`THE_THEOREM1.lean`](Star/Theory/THE_THEOREM1.lean) proves the converse direction, `the_theorem1.completeness1`.
If a relation `φ` is a refinement (`refinament`), and the rules are weakly normalizing, confluent and commute
with the methods, then `φ_ind (φ_flush rule φ) rule` is also a refinement, where `φ_flush` restricts `φ` to
flushed implementation states. So, when the rules satisfy these conditions, a flush-based simulation exists whenever
any simulation does.

[`ARS2.lean`](Star/Theory/ARS2.lean) is an earlier version of the same theory. Its `relation_flush` is the stronger
condition "every internal successor of a flushed state is flushed", it has only the global `enough_star`, and it adds
`Relation.ReflTransGen` variants (`relation_flush'`, `relation_flush_method'`). The allocator case study is built on
it. `ARS.lean` and `ARS2.lean` both declare namespace `ReachingStar` and cannot be imported together.

Conventions: runs record their labels by consing, so in `star` and `star_extend` the most recent event is at the
head of the list. A few lemma names keep historical spellings (`enoght_internal`, `enoght_external`,
`indistinguisability_preservation`, `refinament`).

## Case study 1: the join–join rewrite (`Star/Evaluation/join_join.lean`)

A self-contained model of a dataflow rewrite, in namespace `JoinJoin`. A `join` waits for one value on each of its
two inputs and outputs the pair; each input has a FIFO.

* **Specification `lhs`**: `join1 : join T₁ T₂`, then `join2 : join (T₁ × T₂) T₃`. Its only internal step, `link`,
  moves a pair from `join1` to `join2`.
* **Implementation `rhs`**: `join1 : join T₂ T₃`, then `join2 : join T₁ (T₂ × T₃)`, then `pure`, which
  re-associates `(a, (b, c))` into `((a, b), c)`. Its rules are `link1` and `link2`.

The theorem is **`JoinJoin.rhs_refines_lhs : rhs T₁ T₂ T₃ ⊑ lhs T₁ T₂ T₃`**: everything the new circuit can do, the
old circuit could already do. `⊑` (`Refines`) is a simulation in which the specification may take internal steps
before each observable step. The proof applies `ReachingStar.enough_star_upto` with:

* `method_s`: the specification takes inputs directly and fires `link` exactly once, right before an output, so it
  never holds a pair (`method_s_sound` shows this is a valid way to answer).
* `nf A B C`: the flushed state of `rhs` whose three streams of values (the `T₁`, `T₂` and `T₃` values still
  inside, read from the output backwards) are `A`, `B`, `C`.
* the flush relation, two equations: **`φ₀ i s := q12 = [] ∧ i = nf q0 q1 q2`**. The specification holds no
  pair, and the flushed implementation is the normal form of the specification's three input FIFOs.

The file also defines the direct simulation relation `φ` (the two circuits hold the same three streams, in any
state) and relates the two: `φ₀_iff` shows that `φ₀` is exactly `φ` restricted to flushed implementation states and
specification states holding no pair, `φ₀_implies_φ` gives one direction, and `φ_not_φ₀_unflushed` and
`φ_not_φ₀_pair` show the converse fails. A flushed state is determined by its streams, so the flush relation is
the graph of a function, while `φ` has to compare the two circuits FIFO by FIFO. The module documentation in the
file ("`φ` versus `φ₀`", "Why `φ₀` is enough") explains each proof obligation.

## Case study 2: the Bluespec allocator (`Star/Evaluation/Allocator`)

Lean namespaces: `ReachingStar.Bluespec` (framework and queue example), `M_mkBluealloc` (allocator),
`BluespecPrelude` and `BluespecVerification` (library).

**Framework** ([`Basic.lean`](Star/Evaluation/Allocator/Basic.lean), namespace `ReachingStar.Bluespec`). A Bluespec
module (`Module`) is a state type with internal, unlabelled rules and external methods labelled by an `Event`: a
method name with a `Footprint` (arguments and return value). `ofRule` and `ofAVMethod0/1/2` turn translated Bluespec
functions into transition relations; a method fires only when its ready signal holds. `StructuredRefinement` bundles
the proof obligations: rules strongly normalizing, rules commuting with each other, each method commuting with each
rule, and the three flush conditions. From these, `ReachingStar.Bluespec.enough_star` derives the simulation
(confluence comes from Newman's lemma), and `trace_inclusion_of_initial_refinement` gives trace inclusion from the
initial states.

**Small example** ([`Queue.lean`](Star/Evaluation/Allocator/Queue.lean)). A queue made of two lists, with an internal
rule moving elements from the first to the second, refines a single-list queue:
`ReachingStar.Bluespec.Trivial.refines`.

**The allocator** ([`Example/`](Star/Evaluation/Allocator/Example)). `Bluealloc.bsv` is the Bluespec source of
`mkBluealloc`, a handle allocator with methods `alloc`, `free`, `write_req`, `read_req`, `read_resp`, seven internal
rules, and three dual-port BRAMs (modelled by `Lib/mkSimpleBRAM2.lean`). `mkBluealloc.lean` and
`Bluealloc_types.lean` are its Lean translation.
[`mkBluealloc_refines.lean`](Star/Evaluation/Allocator/Example/mkBluealloc_refines.lean) contains:

* the specification `M_mkBluealloc.Spec`: a store indexed by handles, the set of live handles, and a pending read;
  `alloc` returns any free handle, and using a handle that is not live is undefined behaviour (the specification
  becomes *poisoned* and allows any later behaviour);
* the flush relation `M_mkBluealloc.Refines.phi0`, relating quiescent implementation states (no rule enabled) to valid
  specification states, and any implementation state to a poisoned one;
* the proof obligations, as families of lemmas: 49 rule/rule commutations (`commutes_*`), 35 rule/method
  commutations (`reconverge_*`), 5 `phi0_indistinguishable_*` and 5 `reach_phi0_again_*` lemmas (one per method),
  7 `phi0_reaches_phi0_*` lemmas (one per rule), and termination of the rules (`rules_strongly_normalising`);
* the results:

| Lean name | Statement |
|---|---|
| `M_mkBluealloc.Refines.refines` | `φ_ind phi0` is a simulation between the translated hardware and the specification |
| `M_mkBluealloc.Refines.initial_refines` | every reset state of the hardware is related to the initial specification state |
| `M_mkBluealloc.Refines.trace_refines` | every sequence of method calls (with arguments and results) that the hardware can perform from reset, with any interleaving of internal rules, can also be performed by the specification |

Because of the poisoned state, trace inclusion constrains a trace only up to its first use of a handle that is not
live; after that, only method names and arities are constrained.

## License

Apache 2.0, see [`LICENSE`](LICENSE).
