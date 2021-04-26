# Notes about [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html?back-link=learning.html#book) by Leslie Lamport

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
