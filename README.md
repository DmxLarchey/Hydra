# Hercules kills the Hydra in less the 300 lines of Coq

## The code
This standalone (one file) proof was implemented by Dominique Larchey-Wendling, 
see [`hydra.v`](theories/hydra.v). It is distributed under the terms of the [`MPL-2.0`](LICENSE).

## The battle of Hercules and the Hydra
The Hydra is mainly a _Rose tree_, that is a finite tree with arbitrary branching.
Hercules tries to kill the Hydra by chopping of heads (ie leaves of the Hydra) but 
the Hydra responds in growing copies of specific sub-trees determined by which
head was chopped last.

The Hercules and Hydra game consists in Hercules chopping off head of the Hydra until
the Hydra has no more heads left. In response to a head cut, the Hydra may grow an arbitrary
number of copies of the sub-tree rooted one level below the head that was last chopped
by Hercules.

Importantly, _if Hercules chops a root leaf (ie a leaf just above the root of the Hydra),
then the Hydra cannot morph in response_, it must wait for the next move of Hercules. Absent 
of that rule, the game would possibly not end because no rule would force the number of
nodes to decrease.

There are variants of the game where the number of copies that the Hydra makes is
determined fully by the advancement of the game (eg the number of head that were 
chopped by Hercules so far) by this does not affect the termination property of the
game.

## Rounds vs. moves
In the code of [`hydra.v`](theories/hydra.v), we only model a _round_ which is
the combination of a head cut by Hercules and a conforming response by the Hydra
(see above).
We do not model the moves of Hercules and Hydra independently because:
- while a move of Hercules is nondeterministic and only depends on the current
  shape of the Hydra;
- the response from the Hydra (also possibly nondeterministic), is still
  constrained by which head was chopped off last. The growing of copies of 
  sub-hydras depends on the position of this last chopped head.
  
Modeling this dependency would lengthen the code base because we would need
to represent position of a head inside the Hydra so that Hercules can
transmit that information. By combining Hercules move and the Hydra's
response into the notion of round, the information can be transmitted 
without requiring external information.

