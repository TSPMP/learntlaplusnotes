# Notes about [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book) by Leslie Lamport

## Chapter 1 A Little Simple Math

### Propositional Logic

- mathematics of the two Boolean values `TRUE` and `False` and the operators
  - $\land$ conjunction (and)
  - $\lor$ disjunction (or)
  - $\neg$ negation (not)
  - $\Rightarrow$ implication (implies)
  - $\equiv$ equivalence (is equivalent to)
- precendence of propositonal operators (highest to lowest)
  - $\neg$
  - $\land$ and $\lor$
  - $\Rightarrow$ and $\equiv$
- *tautology (of propositional logic)*: (propositional-logic) formula that is
  true for all possible values of its identifiers

### Sets

- we take as undefined concepts the notion of a set and the relation $\in$
  where $x \in S$ means that $x$ is an element of $S$
- a set can have a finite or infinite number of elements
- two sets are equal iff they have the same elements
- most common operations on sets are
  - $\cap$ intersection
  - $\cup$ union
  - $\subseteq$ subset
  - $\setminus$ set difference

## Predicate Logic

- predicate logic extends propositional logic with the two quantifiers
  - $\forall$ universal quantification (for all)
  - $\exists$ existential quantification (there exists)
- tautology: $\exists x \in S: F \equiv \neg(\forall x \in S: \neg F)$
- tautology: $\forall x \in {}: F$ for any $F$
- $\forall x \in S: F$ and $\exists x \in S: F$ are said to be *bounded*
- bounded and unbounded quantification are related by the following tautologies
  - $(\forall x \in S: F) \equiv (\forall x: (x \in S) \Rightarrow F)$
  - $(\exists x \in S: F) \equiv (\exists x: (x \in S) \land F)$
- tautology: $(\exists x: F) \equiv \neg (\forall x: \neg F)$
- $\forall$ generalizes $\land$
- $\exists$ generalizes $\lor$
- tautologies
  - $(\forall x \in S: F) \land (\forall x \in S: G) \equiv (\forall x \in S: F \land G)$
  - $(\exists x \in S: F) \lor (\exists x \in S: G) \equiv (\exists x \in S: F \lor G)$
- typical abbreviations
  - $\forall x \in S, y \in T: F$ means $\forall x \in S: (\forall y \in T: F)$
  - $\exists x, y \in S: F$ means $\exists x \in S: (\exists y \in S: F)$

## Chapter 2 Specifying a Simple Clock

- like in physics, systems can often be described in terms of their state
- *behavior*: sequence of states
- Sequence of states instead of events. Event is a pair of states.
- Parts of a system description
    - initial predicate: describes conditions for the initial state
    - next-state relation: conditions for a state change and the state change
      itself
- if is an expression
- *action*: formula which contains primed and unprimed variables
- *stuttering steps*: steps which leave the state unchanged. These are necessary
  when we want to relate our system to our systems, e.g. another spec might be a
  refined version in which several things happen within a coarse grain step in
  the first specification. Then, the first spec can only hold true if it allows
  stuttering steps.
- *state*: assignment of values to variables
- *theorem*: a temporal formula which is satisfied by every behavior
- every symbol in a formula must either be a built-in TLA+ operator or it must
  be declared or defined


## Chapter 3 An Asynchronous Interface

- A specification is an abstraction. It describes some aspects of the system and
  ignores others. We want the specification to be as simple as possible, so we
  want to ignore as many details as we can. But, whenever we omit some aspect of
  the system from the specification, we admit a potential source of error. The
  hardest part of writing a specification is choosing the proper abstraction.
- *state function*: ordinary expression with no primed variables or `[]` that
  can contain variables and constants
- *state predicate*: Boolean-valued state function
- *invariant* `Inv` of a spec `Spec` is a state predicate such that
```
Spec => []Inv
```
- *type invariant* `T` of a variable `v`: `v \in T` is an invariant
- set of records
```
[name1: Set1, name2: Set2, ...]
```
- specific instance of that record
```
[name1 |-> v1, name2 |-> v2, ...]
```
- same record as some other record except some fields; `@` refers to the
  corresponding value from the `otherRecord`
```
[otherRecord EXCEPT !.name1 = 1 - @, !.name2 = v3]
```
- user defined operators taking three arguments
```
op(a1, a2, a3) == ...
```
- comments
```
(* inline *)
(*
Spanning multiple
lines
*)
\* end of line
```


## Chapter 4 A FIFO

- `INSTANCE` instantiation is substitution
```
IM == INSTANCE M WITH p1 <- e1, p2 <- e2, ...
```
- parameterized instantiation
```
IM(a) == INSTANCE M with p1 <- e1(a), p2 <- e2(a), ...
```
- implicit substitutions: unspecified replacements will expand automatically to `r <- r`
- instantiation without renaming, e.g. when there is only one instance
```
INSTANCE Channel WITH Data <- D, chan <- x
```
- closed systems: system + environment; usually easier to specify


## Chapter 5 A Caching Memory

- `CHOOSE x: F` equals an arbitrarily chosen value `x` that satisfies formula
  `F`. If no such `x` exists, then the expression has a completely arbitrary
  value
- For any sets `S` and `T`, the set of all functions whose domain equals `S` and
  whose range is any subset of `T` is written `[S -> T]`
- In TLA+, `[x \in S |-> e]` is the function `f` with domain `S` such that `f[x]
  = e`
- `DOMAIN f` is the domain of function `f`
- a record is a function whose domain is a finite set of strings and `r.ack` is
  an abbreviation for `r["ack"]`
- function with multiple arguments can be defined like this
```
f == [n \in Nat, m \in Real |-> n*m]
f[n, m]
```
- recursive function definition
```
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1]
```
- `Spec => [](TypeInvariant /\ Coherence)` does not imply that both
  `TypeInvariant` and `Coherence` are invariants of the next-state action `Next`
  because `THEOREM Coherence /\ [Next]_v => Coherence'` does not necessary hold
  if we had a different `Init` condition. Proving `Coherence`'s invariance is
  not so easy. We must find a predicate `Inv` that is an invariant of `Next`
  such that `Inv` implies `Coherence` and is implied by the initial predicate
  `Init`.
- About "Proving Implementation"
    - Finding concrete "witnesses" for the temporal existential operators and
      substituting them is called *refinement mapping* when the formula holds
      with these substituted values.
    - *step simulation*: find an invariant such that the step in the spec
      implementing another spec is either a `Next` step in the implemented spec
      or a stuttering step in the implemented spec

## Chapter 6 Some More Math

### Sets

- `UNION S`: `S` is a set of sets. Takes the union of all elements of `S`.
- `SUBSET S`: power set of `S`
- `{x \in S: p}`: subset of `S` consisting of all elements `x` satisfying
  property `p`
- `{e: x \in S}`: the set of all elements of form `e` of all elements `x` in `S`
- standard module `FiniteSets`
    - `Cardinality(S)`
    - `IsFiniteSet(S)`
- A collection `C` is too big to be a set if it is as big as the collection of
  allsets — meaning that we can assign to every set a different element of `C`.

### Recursion Revisited

```
f[x \in S] = e
```
is an abbreviation for
```
f == CHOOSE f: [x \in S |-> e]
```
If there is no `f` which satisfies this condition, then the value is
unspecified.

- TLA+ does not allow circular definitions in which two or more functions are
  defined in terms of one another. However, you can convert any mutually
  recursive definition into a single recursive definition of a record-valued
  function whose fields are the desired functions.

### Functions vs Operators

```
Operator(x) == ...
Function[x \in S] == ...
```
- a function by itself is a complete expression which denotes a value but an
  operator is not, e.g. `f \in S` and `f[x] \in S` are syntactically correct but
  `o \in S` is not
- unlike an operator, a function must have a domain, which is a set
- Unlike a function, an operator cannot be defined recursively in TLA+. However,
  we can usually transform an illegal recursive operator definition into a
  nonrecursive one using a recursive function definition.
- Operators also differ from functions in that an operator can take an operator
  as an argument. They can also take infix-operators as an argument (like that
  `_<_`)
- TLA+ does not allow the definition of infix functions.

### Using functions

```
(1) f' = [i \in Nat |-> i + 1]
(2) \A i \in Nat: f'[i] = i + 1
```
are not the same function definition. The (1) is a function definition and (2)
can be satisfied by a lot of different `f`. (1) implies (2) but not vice versa.

### Choose

- the `CHOOSE` operator is known to logicians as Hilbert's epsilon.
- the most common use case is to "name" a uniquely specified value
- can be an unspecified value

## Chapter 7 Writing a Specification: Some Advice

### Why Specify

- the benefit a specification provides must justify the effort
- the purpose of writing a specification is to help avoid errors
- Writing a TLA+ specification can help the design process. Having to describe a
  design precisely often reveals problems - subtle interactions and "corner
  cases" that are easily overlooked.
- A TLA+ specification can provide a clear, concise way of communicating design.
  It helps ensure designers agree on what they have designed, and it provides a
  valuable guide to the engineers who implement and test the system. It may also
  help users understand the system.
- A TLA+ specification is a formal description to which tools can be appliedto
  help find errors in the design and to help in testing the system.

### What to Specify

- a specification is a mathematical model of a particular view of some part of a
  system
- When writing a specification, the first thing you must choose is exactly what
  part of a system you want to model
- The primary purpose of a specification is to help avoid errors. You should
  specify those parts of the system for which a specification is most likely to
  reveal errors.
- TLA+ is particularly effective at revealing concurrency errors—ones that arise
  through the interaction of asynchronous components.

### The Grain of Atomicity

- After choosing what part of the system to specify, you must choose the
  specification’s level of abstraction. The most important aspect of the level
  of abstractionis the grain of atomicity, the choice of what system changes are
  represented as a single step of a behavior.
- The same sequence of system operations is represented by a shorter sequence of
  steps in a coarser-grained representation than in a  finer-grained one. This
  almost always makes the coarser-grained specification simpler than the
  finer-grained one. However, the finer-grained specification more accurately
  describes the behavior of the actual system. A coarser-grained specification
  may fail to reveal important details of the system.
- Let `S1` be the coarser grained spec and `S2` be the finer grained spec, i.e.
  `S1` represents multiple steps in `S2` as a single one.
- Questions to ask
    - Are the sub-steps in `S2` always enabled in a sequential way? Can the
      "first" step appear twice in a row?
    - Are the intermediate steps in the fine grained spec important to the
      problem?
    - More formally: Do the actions *commute*?
- A simple sufficient condition for commutativity of two actions are
    - each one leaves unchanged any variable whose value may be changed by the
      other
    - neither enables or disables the other

### The Data Structures

- Another aspect of a specification’s level of abstraction is the accuracy with
  which it describes the system’s data structures. Describing the data
  structures in more details complicates the specification.
- Question to ask:
    - Does specifying the data structures in more detail help prevent any
      errors?
    - Is TLA+ the right way to catch these kinds of errors?

### Writing the Specification

1. Do always
    - pick the variables
    - define the type invariant
    - define the initial predicate
2. Do when necessary
    - determine constant parameters and assumptions about them
3. Do always writing the next-state action
    - decompose the next-state action as the disjunction of actions describing
      the different kinds of system operations
    - define those actions
    - determine which of the standard modules you need and add the appropriate
      `EXTENDS` statement
4. Do when necessary writing the next-state action
    - sketch a fex example behaviors
    - define state predicates and state functions that are used in several
      different action definitions
    - define constant operators for the data structures you are using
5. Write the temporal part of the specification, i.e. specify the liveness
   properties by choosing the appropriate fairness conditions
6. Assert theorems about the specification
