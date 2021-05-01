# [Teaching Concurrency](http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf) by Leslie Lamport

- computation: sequence of steps
- step: transition from one state to the next
- describe computation needs description of a sequence of states
- more often: describe the set of computations that can be produced by some
  particular computing device
- In practice, describe a set of computations by
    - set of all initial states
    - a next-state relation that describes, for every state, the possible next
      states
- steps are a prerequisite to the most important concept in concurrency:
  invariance
- a computing device does the correct thing only because it maintains a correct
  state
- correctness of the state is expressed by an invariant - a predicate that is
  true in every state of every computation
- a predicate is an invariant is proven by induction: show that it is true in
  every initial state and if it is a true in a state the the next-action
  conserves the conditions in the next state (inductive assertion method)
