# semantic-query
This repository demonstrates semantic query optimization using the chase algorithm. There are two implementations.

   1. The tactic-based one (implemented in LtacChase.v)
   2. The Gallina one implemented in Chase.v

The two have different trade-offs. The Ltac implementation can re-use the wealth of Coq tacics, e.g.
```congruence``` and ```omega```,  to discharge side conditions. Because it reuses Coq's internal representations
it can also support more interesting binding structure, for example nested relations. The down-side of the Ltac
implementation is that it is quite slow compared to the Gallina-based implementation, especially in minimization
where candidates must be back-chased in order to determine equality.


