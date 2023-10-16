# Hercules kills the Hydra in less the 300 lines of Coq

## The code
This standalone (one file) proof was implemented by Dominique Larchey-Wendling, 
see [`hydra.v`](theories/hydra.v). It is distributed under the terms of the [`MPL-2.0`](LICENSE).

## The battle of Hercules and the Hydra
The Hydra is mainly a _Rose tree_, that is a finite tree which arbitrary branching.
Hercules tries to kill the Hydra by chopping of heads (ie leave of the Hydra) but 
the Hydra responds in growing copies of specific sub-trees determined by which
head was cut last.

The Hercules and Hydra game consists in Hercules chopping off head of the Hydra until
the Hydra has no more heads left. In reponse to a head cut, the Hydra may grow an arbitrary
number of copies of the sub-tree rooted one level below the head that was just chopped
by Hercules.

Importantly, _if Hercules chops a root leaf (ie a leaf just above the root of the Hydra),
then the Hydra cannot respond_, it must wait for the next move of Hercules. Absent 
of that rule, the game would possibly not end.

There are variants of the game where the number of copies that the Hydra makes is
determined fully by the advancement of the game (eg the number of previous head cuts
of Hercules) by this does not affect the termination property.

## Rounds vs. moves
In the code of [`hydra.v`](theories/hydra.v), we only model a round which is
the combination of a head cut by Hercules and a conforming response by the Hydra.
We do not model the moves of Hercules and Hydra independently because:
- a move of Hercules is non-deterministic and only depends on the current
  shape of the Hydra;
- the reponse from the Hydra, while also possibly non-deterministic, is still
  constrained by which head was chopped off last. The growing of copies of 
  sub-hydras depend on the position of this last choped head.
  
Modelling this dependency would lengthen the code because we would need
to represent position of head inside a hydra so that Hercules could
transmit that information. By combining Hercules move and the Hydra's
reponse, the information can be transmitted without requirring an
external data-structure.

