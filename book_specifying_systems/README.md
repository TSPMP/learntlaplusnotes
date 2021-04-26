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
